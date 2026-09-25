use std::collections::{BTreeMap, BTreeSet};

use crate::address::SeqNum;
use crate::architecture::Architecture;
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::op::{OpId, OpTreeIter, PcodeOpBank};
use crate::opcodes::OpCode;

#[derive(Clone, Debug, Default)]
pub struct ActionGroupList {
    pub(crate) list: BTreeSet<String>,
}

impl ActionGroupList {
    pub fn contains(&self, nm: &str) -> bool {
        self.list.contains(nm)
    }
}

pub const RULE_REPEATAPPLY: u32 = 4;
pub const RULE_ONCEPERFUNC: u32 = 8;
pub const RULE_ONEACTPERFUNC: u32 = 16;
pub const RULE_DEBUG: u32 = 32;
pub const RULE_WARNINGS_ON: u32 = 64;
pub const RULE_WARNINGS_GIVEN: u32 = 128;

pub const STATUS_START: u32 = 1;
pub const STATUS_BREAKSTARTHIT: u32 = 2;
pub const STATUS_REPEAT: u32 = 4;
pub const STATUS_MID: u32 = 8;
pub const STATUS_END: u32 = 16;
pub const STATUS_ACTIONBREAK: u32 = 32;

pub const BREAK_START: u32 = 1;
pub const TMPBREAK_START: u32 = 2;
pub const BREAK_ACTION: u32 = 4;
pub const TMPBREAK_ACTION: u32 = 8;

#[derive(Clone, Debug)]
pub struct ActionBase {
    pub lcount: i32,
    pub count: i32,
    pub status: u32,
    pub breakpoint: u32,
    pub flags: u32,
    pub count_tests: u32,
    pub count_apply: u32,
    pub name: String,
    pub basegroup: String,
}

impl ActionBase {
    pub fn new(flags: u32, nm: &str, group: &str) -> ActionBase {
        ActionBase {
            lcount: 0,
            count: 0,
            status: STATUS_START,
            breakpoint: 0,
            flags,
            count_tests: 0,
            count_apply: 0,
            name: nm.to_string(),
            basegroup: group.to_string(),
        }
    }
}

fn next_specifyterm(specify: &str) -> (String, String) {
    match specify.find(':') {
        Some(res) => (specify[..res].to_string(), specify[res + 1..].to_string()),
        None => (specify.to_string(), String::new()),
    }
}

fn print_statistics_line(out: &mut String, name: &str, count_tests: u32, count_apply: u32) {
    out.push_str(&format!("{} Tested={} Applied={}\n", name, count_tests, count_apply));
}

pub trait AsDynAction {
    fn as_dyn_action(&mut self) -> &mut dyn Action;
}

impl<T: Action> AsDynAction for T {
    fn as_dyn_action(&mut self) -> &mut dyn Action {
        self
    }
}

pub const MAXIMUM_REPEAT_COUNT: u32 = 100;

fn action_trace_enabled() -> bool {
    static STATE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *STATE.get_or_init(|| std::env::var_os("GHIDRA_ACTION_TRACE").is_some())
}

fn action_trace_dump(data: &Funcdata, glb: &mut Architecture) {
    if std::env::var_os("GHIDRA_ACTION_TRACE_DUMP").is_none() {
        return;
    }
    for op in data.obank.alive_ops() {
        let pcode_op = data.op(op);
        let mut line = format!("{:x}:{} ", pcode_op.get_addr().get_offset(), pcode_op.get_time());
        data.op_print_raw(op, &mut line, glb);
        eprintln!("  {line}");
    }
}

fn action_trace_op(data: &Funcdata, op: OpId) -> String {
    let pcode_op = data.op(op);
    format!("{:x}:{}", pcode_op.get_addr().get_offset(), pcode_op.get_time())
}

pub trait Action: AsDynAction + Send {
    fn base(&self) -> &ActionBase;

    fn base_mut(&mut self) -> &mut ActionBase;

    fn turn_on_debug(&mut self, nm: &str) -> bool {
        if nm == self.base().name {
            self.base_mut().flags |= RULE_DEBUG;
            return true;
        }
        false
    }

    fn turn_off_debug(&mut self, nm: &str) -> bool {
        if nm == self.base().name {
            self.base_mut().flags &= !RULE_DEBUG;
            return true;
        }
        false
    }

    fn print_statistics(&self, out: &mut String) {
        let base = self.base();
        print_statistics_line(out, &base.name, base.count_tests, base.count_apply);
    }

    fn clear_break_points(&mut self) {
        self.base_mut().breakpoint = 0;
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>>;

    fn reset(&mut self, _data: &mut Funcdata, _glb: &mut Architecture) {
        let base = self.base_mut();
        base.status = STATUS_START;
        base.flags &= !RULE_WARNINGS_GIVEN;
    }

    fn reset_stats(&mut self) {
        let base = self.base_mut();
        base.count_tests = 0;
        base.count_apply = 0;
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32>;

    fn print(&self, out: &mut String, num: i32, depth: i32) -> i32 {
        let base = self.base();
        out.push_str(&format!("{:4}", num));
        out.push_str(if (base.flags & RULE_REPEATAPPLY) != 0 {
            " repeat "
        } else {
            "        "
        });
        out.push(if (base.flags & RULE_ONCEPERFUNC) != 0 { '!' } else { ' ' });
        out.push(if (base.breakpoint & (BREAK_START | TMPBREAK_START)) != 0 {
            'S'
        } else {
            ' '
        });
        out.push(if (base.breakpoint & (BREAK_ACTION | TMPBREAK_ACTION)) != 0 {
            'A'
        } else {
            ' '
        });
        for _ in 0..depth * 5 + 2 {
            out.push(' ');
        }
        out.push_str(&base.name);
        num + 1
    }

    fn print_state(&self, out: &mut String) {
        let base = self.base();
        out.push_str(&base.name);
        match base.status {
            STATUS_REPEAT | STATUS_BREAKSTARTHIT | STATUS_START => out.push_str(" start"),
            STATUS_MID => out.push(':'),
            STATUS_END => out.push_str(" end"),
            _ => {}
        }
    }

    fn get_sub_action(&mut self, specify: &str) -> Option<&mut dyn Action> {
        if self.base().name == specify {
            return Some(self.as_dyn_action());
        }
        None
    }

    fn get_sub_rule(&mut self, _specify: &str) -> Option<&mut dyn Rule> {
        None
    }

    fn issue_warning(&mut self, glb: &mut Architecture) {
        let base = self.base_mut();
        if (base.flags & (RULE_WARNINGS_ON | RULE_WARNINGS_GIVEN)) == RULE_WARNINGS_ON {
            base.flags |= RULE_WARNINGS_GIVEN;
            let message = format!("Applied action {}", base.name);
            glb.print_warning(&message);
        }
    }

    fn check_start_break(&mut self) -> bool {
        let base = self.base_mut();
        if (base.breakpoint & (BREAK_START | TMPBREAK_START)) != 0 {
            base.breakpoint &= !TMPBREAK_START;
            return true;
        }
        false
    }

    fn check_action_break(&mut self) -> bool {
        let base = self.base_mut();
        if (base.breakpoint & (BREAK_ACTION | TMPBREAK_ACTION)) != 0 {
            base.breakpoint &= !TMPBREAK_ACTION;
            return true;
        }
        false
    }

    fn turn_on_warnings(&mut self) {
        self.base_mut().flags |= RULE_WARNINGS_ON;
    }

    fn turn_off_warnings(&mut self) {
        self.base_mut().flags &= !RULE_WARNINGS_ON;
    }

    fn perform(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut repeat_count: u32 = 0;
        loop {
            let status = self.base().status;
            let mut run_apply = false;
            match status {
                STATUS_START => {
                    self.base_mut().count = 0;
                    if self.check_start_break() {
                        self.base_mut().status = STATUS_BREAKSTARTHIT;
                        return Ok(-1);
                    }
                    let base = self.base_mut();
                    base.count_tests += 1;
                    base.lcount = base.count;
                    run_apply = true;
                }
                STATUS_BREAKSTARTHIT | STATUS_REPEAT => {
                    let base = self.base_mut();
                    base.lcount = base.count;
                    run_apply = true;
                }
                STATUS_MID => {
                    run_apply = true;
                }
                STATUS_END => {
                    return Ok(0);
                }
                _ => {}
            }
            if run_apply {
                let res = self.apply(data, glb)?;
                if res < 0 {
                    self.base_mut().status = STATUS_MID;
                    return Ok(res);
                } else if self.base().lcount < self.base().count {
                    if action_trace_enabled() {
                        eprintln!("A {} {}", self.get_name(), self.base().count - self.base().lcount);
                        action_trace_dump(data, glb);
                    }
                    self.issue_warning(glb);
                    self.base_mut().count_apply += 1;
                    if self.check_action_break() {
                        self.base_mut().status = STATUS_ACTIONBREAK;
                        return Ok(-1);
                    }
                }
            }
            self.base_mut().status = STATUS_REPEAT;
            let base = self.base();
            if !(base.lcount < base.count && (base.flags & RULE_REPEATAPPLY) != 0) {
                break;
            }
            repeat_count += 1;
            if repeat_count >= MAXIMUM_REPEAT_COUNT {
                let message = format!("Exceeded maximum repeat count for action {}", self.get_name());
                data.warning_header(&message, glb);
                break;
            }
        }

        let base = self.base_mut();
        if (base.flags & (RULE_ONCEPERFUNC | RULE_ONEACTPERFUNC)) != 0 {
            if base.count > 0 || (base.flags & RULE_ONCEPERFUNC) != 0 {
                base.status = STATUS_END;
            } else {
                base.status = STATUS_START;
            }
        } else {
            base.status = STATUS_START;
        }
        Ok(base.count)
    }

    fn set_break_point(&mut self, tp: u32, specify: &str) -> bool {
        if let Some(res) = self.get_sub_action(specify) {
            res.base_mut().breakpoint |= tp;
            return true;
        }
        if let Some(rule) = self.get_sub_rule(specify) {
            rule.set_break(tp);
            return true;
        }
        false
    }

    fn set_warning(&mut self, val: bool, specify: &str) -> bool {
        if let Some(res) = self.get_sub_action(specify) {
            if val {
                res.turn_on_warnings();
            } else {
                res.turn_off_warnings();
            }
            return true;
        }
        if let Some(rule) = self.get_sub_rule(specify) {
            if val {
                rule.turn_on_warnings();
            } else {
                rule.turn_off_warnings();
            }
            return true;
        }
        false
    }

    fn disable_rule(&mut self, specify: &str) -> bool {
        if let Some(rule) = self.get_sub_rule(specify) {
            rule.set_disable();
            return true;
        }
        false
    }

    fn enable_rule(&mut self, specify: &str) -> bool {
        if let Some(rule) = self.get_sub_rule(specify) {
            rule.clear_disable();
            return true;
        }
        false
    }

    fn get_name(&self) -> &str {
        &self.base().name
    }

    fn get_group(&self) -> &str {
        &self.base().basegroup
    }

    fn get_status(&self) -> u32 {
        self.base().status
    }

    fn get_num_tests(&self) -> u32 {
        self.base().count_tests
    }

    fn get_num_apply(&self) -> u32 {
        self.base().count_apply
    }
}

enum GroupMatch {
    This,
    Child(usize, String),
    Nothing,
}

fn group_sub_action_match(name: &str, list: &mut [Box<dyn Action>], specify: &str) -> GroupMatch {
    let (token, mut remain) = next_specifyterm(specify);
    if name == token {
        if remain.is_empty() {
            return GroupMatch::This;
        }
    } else {
        remain = specify.to_string();
    }
    let mut lastaction = None;
    let mut matchcount = 0;
    for (index, child) in list.iter_mut().enumerate() {
        if child.get_sub_action(&remain).is_some() {
            lastaction = Some(index);
            matchcount += 1;
            if matchcount > 1 {
                return GroupMatch::Nothing;
            }
        }
    }
    match lastaction {
        Some(index) => GroupMatch::Child(index, remain),
        None => GroupMatch::Nothing,
    }
}

fn group_sub_rule<'a>(name: &str, list: &'a mut [Box<dyn Action>], specify: &str) -> Option<&'a mut dyn Rule> {
    let (token, mut remain) = next_specifyterm(specify);
    if name == token {
        if remain.is_empty() {
            return None;
        }
    } else {
        remain = specify.to_string();
    }
    let mut lastrule = None;
    let mut matchcount = 0;
    for (index, child) in list.iter_mut().enumerate() {
        if child.get_sub_rule(&remain).is_some() {
            lastrule = Some(index);
            matchcount += 1;
            if matchcount > 1 {
                return None;
            }
        }
    }
    match lastrule {
        Some(index) => list[index].get_sub_rule(&remain),
        None => None,
    }
}

pub struct ActionGroup {
    pub base: ActionBase,
    pub list: Vec<Box<dyn Action>>,
    pub state: usize,
}

impl ActionGroup {
    pub fn new(flags: u32, nm: &str) -> ActionGroup {
        ActionGroup {
            base: ActionBase::new(flags, nm, ""),
            list: Vec::new(),
            state: usize::MAX,
        }
    }

    pub fn add_action(&mut self, ac: Box<dyn Action>) {
        self.list.push(ac);
    }

    fn clone_children(&self, grouplist: &ActionGroupList) -> Vec<Box<dyn Action>> {
        let mut res = Vec::new();
        for child in self.list.iter() {
            if let Some(ac) = child.clone_action(grouplist) {
                res.push(ac);
            }
        }
        res
    }
}

impl Action for ActionGroup {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clear_break_points(&mut self) {
        for child in self.list.iter_mut() {
            child.clear_break_points();
        }
        self.base.breakpoint = 0;
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        let children = self.clone_children(grouplist);
        if children.is_empty() {
            return None;
        }
        let mut res = ActionGroup::new(self.base.flags, &self.base.name);
        for ac in children {
            res.add_action(ac);
        }
        Some(Box::new(res))
    }

    fn reset(&mut self, data: &mut Funcdata, glb: &mut Architecture) {
        self.base.status = STATUS_START;
        self.base.flags &= !RULE_WARNINGS_GIVEN;
        for child in self.list.iter_mut() {
            child.reset(data, glb);
        }
    }

    fn reset_stats(&mut self) {
        self.base.count_tests = 0;
        self.base.count_apply = 0;
        for child in self.list.iter_mut() {
            child.reset_stats();
        }
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if self.base.status != STATUS_MID {
            self.state = 0;
        }
        while self.state < self.list.len() {
            let res = self.list[self.state].perform(data, glb)?;
            if res > 0 {
                self.base.count += res;
                if self.check_action_break() {
                    self.state += 1;
                    return Ok(-1);
                }
            } else if res < 0 {
                return Ok(-1);
            }
            self.state += 1;
        }
        Ok(0)
    }

    fn print(&self, out: &mut String, num: i32, depth: i32) -> i32 {
        let base = &self.base;
        let mut num = num;
        out.push_str(&format!("{:4}", num));
        out.push_str(if (base.flags & RULE_REPEATAPPLY) != 0 {
            " repeat "
        } else {
            "        "
        });
        out.push(if (base.flags & RULE_ONCEPERFUNC) != 0 { '!' } else { ' ' });
        out.push(if (base.breakpoint & (BREAK_START | TMPBREAK_START)) != 0 {
            'S'
        } else {
            ' '
        });
        out.push(if (base.breakpoint & (BREAK_ACTION | TMPBREAK_ACTION)) != 0 {
            'A'
        } else {
            ' '
        });
        for _ in 0..depth * 5 + 2 {
            out.push(' ');
        }
        out.push_str(&base.name);
        num += 1;
        out.push('\n');
        for (index, child) in self.list.iter().enumerate() {
            num = child.print(out, num, depth + 1);
            if self.state == index {
                out.push_str("  <-- ");
            }
            out.push('\n');
        }
        num
    }

    fn print_state(&self, out: &mut String) {
        out.push_str(&self.base.name);
        match self.base.status {
            STATUS_REPEAT | STATUS_BREAKSTARTHIT | STATUS_START => out.push_str(" start"),
            STATUS_MID => out.push(':'),
            STATUS_END => out.push_str(" end"),
            _ => {}
        }
        if self.base.status == STATUS_MID
            && let Some(subact) = self.list.get(self.state)
        {
            subact.print_state(out);
        }
    }

    fn get_sub_action(&mut self, specify: &str) -> Option<&mut dyn Action> {
        match group_sub_action_match(&self.base.name, &mut self.list, specify) {
            GroupMatch::This => Some(self),
            GroupMatch::Child(index, remain) => self.list[index].get_sub_action(&remain),
            GroupMatch::Nothing => None,
        }
    }

    fn get_sub_rule(&mut self, specify: &str) -> Option<&mut dyn Rule> {
        group_sub_rule(&self.base.name, &mut self.list, specify)
    }

    fn turn_on_debug(&mut self, nm: &str) -> bool {
        if nm == self.base.name {
            self.base.flags |= RULE_DEBUG;
            return true;
        }
        for child in self.list.iter_mut() {
            if child.turn_on_debug(nm) {
                return true;
            }
        }
        false
    }

    fn turn_off_debug(&mut self, nm: &str) -> bool {
        if nm == self.base.name {
            self.base.flags &= !RULE_DEBUG;
            return true;
        }
        for child in self.list.iter_mut() {
            if child.turn_off_debug(nm) {
                return true;
            }
        }
        false
    }

    fn print_statistics(&self, out: &mut String) {
        print_statistics_line(out, &self.base.name, self.base.count_tests, self.base.count_apply);
        for child in self.list.iter() {
            child.print_statistics(out);
        }
    }
}

pub struct ActionRestartGroup {
    pub group: ActionGroup,
    pub maxrestarts: i32,
    pub curstart: i32,
}

impl ActionRestartGroup {
    pub fn new(flags: u32, nm: &str, max: i32) -> ActionRestartGroup {
        ActionRestartGroup {
            group: ActionGroup::new(flags, nm),
            maxrestarts: max,
            curstart: 0,
        }
    }

    pub fn add_action(&mut self, ac: Box<dyn Action>) {
        self.group.add_action(ac);
    }
}

impl Action for ActionRestartGroup {
    fn base(&self) -> &ActionBase {
        &self.group.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.group.base
    }

    fn clear_break_points(&mut self) {
        self.group.clear_break_points();
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        let children = self.group.clone_children(grouplist);
        if children.is_empty() {
            return None;
        }
        let mut res = ActionRestartGroup::new(self.group.base.flags, &self.group.base.name, self.maxrestarts);
        for ac in children {
            res.add_action(ac);
        }
        Some(Box::new(res))
    }

    fn reset(&mut self, data: &mut Funcdata, glb: &mut Architecture) {
        self.curstart = 0;
        self.group.reset(data, glb);
    }

    fn reset_stats(&mut self) {
        self.group.reset_stats();
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if self.curstart == -1 {
            return Ok(0);
        }
        loop {
            let res = self.group.apply(data, glb)?;
            if res != 0 {
                return Ok(res);
            }
            if !data.has_restart_pending() {
                self.curstart = -1;
                return Ok(0);
            }
            if data.is_jumptable_recovery_on() {
                return Ok(0);
            }
            self.curstart += 1;
            if self.curstart > self.maxrestarts {
                data.warning_header("Exceeded maximum restarts with more pending", glb);
                self.curstart = -1;
                return Ok(0);
            }
            glb.clear_analysis(data);
            for child in self.group.list.iter_mut() {
                child.reset(data, glb);
            }
            self.group.base.status = STATUS_START;
        }
    }

    fn print(&self, out: &mut String, num: i32, depth: i32) -> i32 {
        self.group.print(out, num, depth)
    }

    fn print_state(&self, out: &mut String) {
        self.group.print_state(out);
    }

    fn get_sub_action(&mut self, specify: &str) -> Option<&mut dyn Action> {
        match group_sub_action_match(&self.group.base.name, &mut self.group.list, specify) {
            GroupMatch::This => Some(self),
            GroupMatch::Child(index, remain) => self.group.list[index].get_sub_action(&remain),
            GroupMatch::Nothing => None,
        }
    }

    fn get_sub_rule(&mut self, specify: &str) -> Option<&mut dyn Rule> {
        self.group.get_sub_rule(specify)
    }

    fn turn_on_debug(&mut self, nm: &str) -> bool {
        self.group.turn_on_debug(nm)
    }

    fn turn_off_debug(&mut self, nm: &str) -> bool {
        self.group.turn_off_debug(nm)
    }

    fn print_statistics(&self, out: &mut String) {
        self.group.print_statistics(out);
    }
}

pub const TYPE_DISABLE: u32 = 1;
pub const RULE_TYPE_DEBUG: u32 = 2;
pub const WARNINGS_ON: u32 = 4;
pub const WARNINGS_GIVEN: u32 = 8;

#[derive(Clone, Debug)]
pub struct RuleBase {
    pub flags: u32,
    pub breakpoint: u32,
    pub name: String,
    pub basegroup: String,
    pub count_tests: u32,
    pub count_apply: u32,
}

impl RuleBase {
    pub fn new(group: &str, fl: u32, nm: &str) -> RuleBase {
        RuleBase {
            flags: fl,
            breakpoint: 0,
            name: nm.to_string(),
            basegroup: group.to_string(),
            count_tests: 0,
            count_apply: 0,
        }
    }
}

pub trait Rule: Send {
    fn base(&self) -> &RuleBase;

    fn base_mut(&mut self) -> &mut RuleBase;

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>>;

    fn get_op_list(&self, oplist: &mut Vec<OpCode>);

    fn apply_op(&mut self, _op: OpId, _data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        Ok(0)
    }

    fn reset(&mut self, _data: &mut Funcdata, _glb: &mut Architecture) {
        self.base_mut().flags &= !WARNINGS_GIVEN;
    }

    fn reset_stats(&mut self) {
        let base = self.base_mut();
        base.count_tests = 0;
        base.count_apply = 0;
    }

    fn print_statistics(&self, out: &mut String) {
        let base = self.base();
        print_statistics_line(out, &base.name, base.count_tests, base.count_apply);
    }

    fn turn_on_debug(&mut self, nm: &str) -> bool {
        if nm == self.base().name {
            self.base_mut().flags |= RULE_TYPE_DEBUG;
            return true;
        }
        false
    }

    fn turn_off_debug(&mut self, nm: &str) -> bool {
        if nm == self.base().name {
            self.base_mut().flags &= !RULE_TYPE_DEBUG;
            return true;
        }
        false
    }

    fn issue_warning(&mut self, glb: &mut Architecture) {
        let base = self.base_mut();
        if (base.flags & (WARNINGS_ON | WARNINGS_GIVEN)) == WARNINGS_ON {
            base.flags |= WARNINGS_GIVEN;
            let message = format!("Applied rule {}", base.name);
            glb.print_warning(&message);
        }
    }

    fn get_name(&self) -> &str {
        &self.base().name
    }

    fn get_group(&self) -> &str {
        &self.base().basegroup
    }

    fn get_num_tests(&self) -> u32 {
        self.base().count_tests
    }

    fn get_num_apply(&self) -> u32 {
        self.base().count_apply
    }

    fn set_break(&mut self, tp: u32) {
        self.base_mut().breakpoint |= tp;
    }

    fn clear_break(&mut self, tp: u32) {
        self.base_mut().breakpoint &= !tp;
    }

    fn clear_break_points(&mut self) {
        self.base_mut().breakpoint = 0;
    }

    fn turn_on_warnings(&mut self) {
        self.base_mut().flags |= WARNINGS_ON;
    }

    fn turn_off_warnings(&mut self) {
        self.base_mut().flags &= !WARNINGS_ON;
    }

    fn is_disabled(&self) -> bool {
        (self.base().flags & TYPE_DISABLE) != 0
    }

    fn set_disable(&mut self) {
        self.base_mut().flags |= TYPE_DISABLE;
    }

    fn clear_disable(&mut self) {
        self.base_mut().flags &= !TYPE_DISABLE;
    }

    fn check_action_break(&mut self) -> bool {
        let base = self.base_mut();
        if (base.breakpoint & (BREAK_ACTION | TMPBREAK_ACTION)) != 0 {
            base.breakpoint &= !TMPBREAK_ACTION;
            return true;
        }
        false
    }

    fn get_break_point(&self) -> u32 {
        self.base().breakpoint
    }
}

pub struct ActionPool {
    pub base: ActionBase,
    pub allrules: Vec<Box<dyn Rule>>,
    pub perop: Vec<Vec<usize>>,
    pub op_state: OpTreeIter,
    pub current_seq: Option<SeqNum>,
    pub rule_index: i32,
}

impl ActionPool {
    pub fn new(flags: u32, nm: &str) -> ActionPool {
        ActionPool {
            base: ActionBase::new(flags, nm, ""),
            allrules: Vec::new(),
            perop: vec![Vec::new(); OpCode::Max.index()],
            op_state: None,
            current_seq: None,
            rule_index: 0,
        }
    }

    fn advance_op_state(&mut self, data: &Funcdata) {
        self.op_state = PcodeOpBank::tree_next(&data.obank.optree, &self.op_state);
    }

    pub fn process_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.op(op).is_dead() {
            self.advance_op_state(data);
            data.op_dead_and_gone(op)?;
            self.rule_index = 0;
            return Ok(0);
        }
        let mut opc = data.op(op).code();
        while (self.rule_index as usize) < self.perop[opc.index()].len() {
            let rule_slot = self.perop[opc.index()][self.rule_index as usize];
            self.rule_index += 1;
            let rl = &mut self.allrules[rule_slot];
            if rl.is_disabled() {
                continue;
            }
            rl.base_mut().count_tests += 1;
            let res = rl.apply_op(op, data, glb)?;
            if res > 0 {
                if action_trace_enabled() {
                    eprintln!("R {} {}", rl.get_name(), action_trace_op(data, op));
                    action_trace_dump(data, glb);
                }
                rl.base_mut().count_apply += 1;
                self.base.count += res;
                rl.issue_warning(glb);
                if rl.check_action_break() {
                    return Ok(-1);
                }
                if data.op(op).is_dead() {
                    break;
                }
                if opc != data.op(op).code() {
                    opc = data.op(op).code();
                    self.rule_index = 0;
                }
            }
        }
        self.advance_op_state(data);
        self.rule_index = 0;
        Ok(0)
    }

    pub fn add_rule(&mut self, rl: Box<dyn Rule>) {
        let mut oplist = Vec::new();
        rl.get_op_list(&mut oplist);
        let slot = self.allrules.len();
        self.allrules.push(rl);
        for opc in oplist {
            self.perop[opc.index()].push(slot);
        }
    }
}

impl Action for ActionPool {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clear_break_points(&mut self) {
        for rule in self.allrules.iter_mut() {
            rule.clear_break_points();
        }
        self.base.breakpoint = 0;
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        let mut res: Option<ActionPool> = None;
        for rule in self.allrules.iter() {
            if let Some(rl) = rule.clone_rule(grouplist) {
                res.get_or_insert_with(|| ActionPool::new(self.base.flags, &self.base.name))
                    .add_rule(rl);
            }
        }
        res.map(|pool| Box::new(pool) as Box<dyn Action>)
    }

    fn reset(&mut self, data: &mut Funcdata, glb: &mut Architecture) {
        self.base.status = STATUS_START;
        self.base.flags &= !RULE_WARNINGS_GIVEN;
        for rule in self.allrules.iter_mut() {
            rule.reset(data, glb);
        }
    }

    fn reset_stats(&mut self) {
        self.base.count_tests = 0;
        self.base.count_apply = 0;
        for rule in self.allrules.iter_mut() {
            rule.reset_stats();
        }
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if self.base.status != STATUS_MID {
            self.op_state = data.begin_op_main();
            self.rule_index = 0;
        }
        while self.op_state != data.end_op_main() {
            match PcodeOpBank::tree_at(&data.obank.optree, &self.op_state) {
                Some(op) => {
                    self.current_seq = Some(data.op(op).get_seq_num().clone());
                    if self.process_op(op, data, glb)? != 0 {
                        return Ok(-1);
                    }
                }
                None => {
                    self.advance_op_state(data);
                    self.rule_index = 0;
                }
            }
        }
        Ok(0)
    }

    fn print(&self, out: &mut String, num: i32, depth: i32) -> i32 {
        let base = &self.base;
        let mut num = num;
        out.push_str(&format!("{:4}", num));
        out.push_str(if (base.flags & RULE_REPEATAPPLY) != 0 {
            " repeat "
        } else {
            "        "
        });
        out.push(if (base.flags & RULE_ONCEPERFUNC) != 0 { '!' } else { ' ' });
        out.push(if (base.breakpoint & (BREAK_START | TMPBREAK_START)) != 0 {
            'S'
        } else {
            ' '
        });
        out.push(if (base.breakpoint & (BREAK_ACTION | TMPBREAK_ACTION)) != 0 {
            'A'
        } else {
            ' '
        });
        for _ in 0..depth * 5 + 2 {
            out.push(' ');
        }
        out.push_str(&base.name);
        num += 1;
        out.push('\n');
        let depth = depth + 1;
        for rl in self.allrules.iter() {
            out.push_str(&format!("{:4}", num));
            out.push(if rl.is_disabled() { 'D' } else { ' ' });
            out.push(if (rl.get_break_point() & (BREAK_ACTION | TMPBREAK_ACTION)) != 0 {
                'A'
            } else {
                ' '
            });
            for _ in 0..depth * 5 + 2 {
                out.push(' ');
            }
            out.push_str(rl.get_name());
            out.push('\n');
            num += 1;
        }
        num
    }

    fn print_state(&self, out: &mut String) {
        out.push_str(&self.base.name);
        match self.base.status {
            STATUS_REPEAT | STATUS_BREAKSTARTHIT | STATUS_START => out.push_str(" start"),
            STATUS_MID => out.push(':'),
            STATUS_END => out.push_str(" end"),
            _ => {}
        }
        if self.base.status == STATUS_MID
            && let Some(seq) = &self.current_seq
        {
            out.push_str(&format!(" {}", seq));
        }
    }

    fn get_sub_rule(&mut self, specify: &str) -> Option<&mut dyn Rule> {
        let (token, mut remain) = next_specifyterm(specify);
        if self.base.name == token {
            if remain.is_empty() {
                return None;
            }
        } else {
            remain = specify.to_string();
        }
        let mut lastrule = None;
        let mut matchcount = 0;
        for (index, testrule) in self.allrules.iter().enumerate() {
            if testrule.get_name() == remain {
                lastrule = Some(index);
                matchcount += 1;
                if matchcount > 1 {
                    return None;
                }
            }
        }
        match lastrule {
            Some(index) => Some(self.allrules[index].as_mut()),
            None => None,
        }
    }

    fn print_statistics(&self, out: &mut String) {
        print_statistics_line(out, &self.base.name, self.base.count_tests, self.base.count_apply);
        for rule in self.allrules.iter() {
            rule.print_statistics(out);
        }
    }

    fn turn_on_debug(&mut self, nm: &str) -> bool {
        if nm == self.base.name {
            self.base.flags |= RULE_DEBUG;
            return true;
        }
        for rule in self.allrules.iter_mut() {
            if rule.turn_on_debug(nm) {
                return true;
            }
        }
        false
    }

    fn turn_off_debug(&mut self, nm: &str) -> bool {
        if nm == self.base.name {
            self.base.flags &= !RULE_DEBUG;
            return true;
        }
        for rule in self.allrules.iter_mut() {
            if rule.turn_off_debug(nm) {
                return true;
            }
        }
        false
    }
}

pub const UNIVERSALNAME: &str = "universal";

#[derive(Default)]
pub struct ActionDatabase {
    pub currentact: Option<String>,
    pub currentactname: String,
    pub groupmap: BTreeMap<String, ActionGroupList>,
    pub actionmap: BTreeMap<String, Box<dyn Action>>,
    pub is_default_groups: bool,
}

impl ActionDatabase {
    pub fn new() -> ActionDatabase {
        ActionDatabase {
            currentact: None,
            currentactname: String::new(),
            groupmap: BTreeMap::new(),
            actionmap: BTreeMap::new(),
            is_default_groups: false,
        }
    }

    pub fn register_action(&mut self, nm: &str, act: Box<dyn Action>) {
        self.actionmap.insert(nm.to_string(), act);
    }

    pub fn build_default_groups(&mut self) {
        if self.is_default_groups {
            return;
        }
        self.groupmap.clear();
        let members = [
            "base",
            "protorecovery",
            "protorecovery_a",
            "deindirect",
            "localrecovery",
            "deadcode",
            "typerecovery",
            "stackptrflow",
            "blockrecovery",
            "stackvars",
            "deadcontrolflow",
            "switchnorm",
            "cleanup",
            "splitcopy",
            "splitpointer",
            "merge",
            "dynamic",
            "casts",
            "analysis",
            "fixateglobals",
            "fixateproto",
            "constsequence",
            "bitfields",
            "segment",
            "returnsplit",
            "nodejoin",
            "doubleload",
            "doubleprecis",
            "unreachable",
            "subvar",
            "floatprecision",
            "conditionalexe",
            "",
        ];
        self.set_group("decompile", &members);

        let jumptab = [
            "base",
            "noproto",
            "localrecovery",
            "deadcode",
            "stackptrflow",
            "stackvars",
            "analysis",
            "segment",
            "subvar",
            "normalizebranches",
            "conditionalexe",
            "",
        ];
        self.set_group("jumptable", &jumptab);

        let normali = [
            "base",
            "protorecovery",
            "protorecovery_b",
            "deindirect",
            "localrecovery",
            "deadcode",
            "stackptrflow",
            "normalanalysis",
            "stackvars",
            "deadcontrolflow",
            "analysis",
            "fixateproto",
            "nodejoin",
            "unreachable",
            "subvar",
            "floatprecision",
            "normalizebranches",
            "conditionalexe",
            "",
        ];
        self.set_group("normalize", &normali);

        let paramid = [
            "base",
            "protorecovery",
            "protorecovery_b",
            "deindirect",
            "localrecovery",
            "deadcode",
            "typerecovery",
            "stackptrflow",
            "siganalysis",
            "stackvars",
            "deadcontrolflow",
            "analysis",
            "fixateproto",
            "unreachable",
            "subvar",
            "floatprecision",
            "conditionalexe",
            "",
        ];
        self.set_group("paramid", &paramid);

        let regmemb = ["base", "analysis", "subvar", ""];
        self.set_group("register", &regmemb);

        let firstmem = ["base", ""];
        self.set_group("firstpass", &firstmem);
        self.is_default_groups = true;
    }

    pub fn get_action(&mut self, nm: &str) -> Result<&mut Box<dyn Action>> {
        match self.actionmap.get_mut(nm) {
            None => Err(Error::Lowlevel(format!("No registered action: {}", nm))),
            Some(act) => Ok(act),
        }
    }

    pub fn derive_action(&mut self, baseaction: &str, grp: &str) -> Result<Option<String>> {
        if self.actionmap.contains_key(grp) {
            return Ok(Some(grp.to_string()));
        }
        let curgrp = self.get_group(grp)?.clone();
        let newact = self.get_action(baseaction)?.clone_action(&curgrp);
        match newact {
            None => Ok(None),
            Some(newact) => {
                self.register_action(grp, newact);
                Ok(Some(grp.to_string()))
            }
        }
    }

    pub fn reset_defaults(&mut self) -> Result<()> {
        let universal_action = self.actionmap.remove(UNIVERSALNAME);
        self.actionmap.clear();
        if let Some(universal_action) = universal_action {
            self.register_action(UNIVERSALNAME, universal_action);
        }
        self.build_default_groups();
        self.set_current("decompile")?;
        Ok(())
    }

    pub fn get_current(&mut self) -> Option<&mut Box<dyn Action>> {
        let name = self.currentact.as_ref()?;
        self.actionmap.get_mut(name)
    }

    pub fn get_current_name(&self) -> &str {
        &self.currentactname
    }

    pub fn get_group(&self, grp: &str) -> Result<&ActionGroupList> {
        match self.groupmap.get(grp) {
            None => Err(Error::Lowlevel(format!("Action group does not exist: {}", grp))),
            Some(group) => Ok(group),
        }
    }

    pub fn set_current(&mut self, actname: &str) -> Result<Option<&mut Box<dyn Action>>> {
        self.currentactname = actname.to_string();
        self.currentact = self.derive_action(UNIVERSALNAME, actname)?;
        Ok(self.get_current())
    }

    pub fn toggle_action(&mut self, grp: &str, basegrp: &str, val: bool) -> Result<Option<&mut Box<dyn Action>>> {
        self.get_action(UNIVERSALNAME)?;
        if val {
            self.add_to_group(grp, basegrp);
        } else {
            self.remove_from_group(grp, basegrp);
        }
        let curgrp = self.get_group(grp)?.clone();
        let newact = self.get_action(UNIVERSALNAME)?.clone_action(&curgrp);
        let registered = match newact {
            None => {
                self.actionmap.remove(grp);
                None
            }
            Some(newact) => {
                self.register_action(grp, newact);
                Some(grp.to_string())
            }
        };
        if grp == self.currentactname {
            self.currentact = registered.clone();
        }
        match registered {
            None => Ok(None),
            Some(name) => Ok(self.actionmap.get_mut(&name)),
        }
    }

    pub fn set_group(&mut self, grp: &str, argv: &[&str]) {
        let curgrp = self.groupmap.entry(grp.to_string()).or_default();
        curgrp.list.clear();
        for member in argv {
            if member.is_empty() {
                break;
            }
            curgrp.list.insert(member.to_string());
        }
        self.is_default_groups = false;
    }

    pub fn clone_group(&mut self, oldname: &str, newname: &str) -> Result<()> {
        let curgrp = self.get_group(oldname)?.clone();
        self.groupmap.insert(newname.to_string(), curgrp);
        self.is_default_groups = false;
        Ok(())
    }

    pub fn add_to_group(&mut self, grp: &str, basegroup: &str) -> bool {
        self.is_default_groups = false;
        let curgrp = self.groupmap.entry(grp.to_string()).or_default();
        curgrp.list.insert(basegroup.to_string())
    }

    pub fn remove_from_group(&mut self, grp: &str, basegrp: &str) -> bool {
        self.is_default_groups = false;
        let curgrp = self.groupmap.entry(grp.to_string()).or_default();
        curgrp.list.remove(basegrp)
    }

    pub fn universal_action(&mut self, conf: &mut Architecture) {
        let stackspace = conf.manager.get_stack_space();
        let mut act = ActionRestartGroup::new(RULE_ONCEPERFUNC, "universal", 1);
        act.add_action(Box::new(crate::coreaction::ActionStart::new("base")));
        act.add_action(Box::new(crate::coreaction::ActionConstbase::new("base")));
        act.add_action(Box::new(crate::coreaction::ActionNormalizeSetup::new("normalanalysis")));
        act.add_action(Box::new(crate::coreaction::ActionDefaultParams::new("base")));
        act.add_action(Box::new(crate::coreaction::ActionExtraPopSetup::new(
            "base",
            stackspace.clone(),
        )));
        act.add_action(Box::new(crate::coreaction::ActionPrototypeTypes::new("protorecovery")));
        act.add_action(Box::new(crate::coreaction::ActionFuncLink::new("protorecovery")));
        act.add_action(Box::new(crate::coreaction::ActionFuncLinkOutOnly::new("noproto")));
        let mut actfullloop = ActionGroup::new(RULE_REPEATAPPLY, "fullloop");
        let mut actmainloop = ActionGroup::new(RULE_REPEATAPPLY, "mainloop");
        actmainloop.add_action(Box::new(crate::coreaction::ActionUnreachable::new("base")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionVarnodeProps::new("base")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionHeritage::new("base")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionParamDouble::new("protorecovery")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionSegmentize::new("base")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionInternalStorage::new("base")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionForceGoto::new("blockrecovery")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionDirectWrite::new(
            "protorecovery_a",
            true,
        )));
        actmainloop.add_action(Box::new(crate::coreaction::ActionDirectWrite::new(
            "protorecovery_b",
            false,
        )));
        actmainloop.add_action(Box::new(crate::coreaction::ActionActiveParam::new("protorecovery")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionReturnRecovery::new("protorecovery")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionRestrictLocal::new("localrecovery")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionDeadCode::new("deadcode")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionDynamicMapping::new("dynamic")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionSpacebase::new("base")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionNonzeroMask::new("analysis")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionInferTypes::new("typerecovery")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionRestructureVarnode::new(
            "localrecovery",
        )));
        let mut actstackstall = ActionGroup::new(RULE_REPEATAPPLY, "stackstall");
        let mut actprop = ActionPool::new(RULE_REPEATAPPLY, "oppool1");
        actprop.add_rule(Box::new(crate::ruleaction::RuleEarlyRemoval::new("deadcode")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleTermOrder::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSelectCse::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleCollectTerms::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePullsubMulti::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePullsubIndirect::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePushMulti::new("nodejoin")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSborrow::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleScarry::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleIntLessEqual::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleTrivialArith::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleTrivialBool::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleTrivialShift::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSignShift::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleTestSign::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleIdentityEl::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleOrMask::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleAndMask::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleOrConsume::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleOrCollapse::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleAndOrLump::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleShiftBitops::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleRightShiftAnd::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleNotDistribute::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleHighOrderAnd::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleAndDistribute::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleAndCommute::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleAndPiece::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleAndZext::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleAndCompare::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleDoubleSub::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleDoubleShift::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleDoubleArithShift::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleConcatShift::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleLeftRight::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleShiftCompare::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleShift2Mult::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleShiftPiece::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleMultiCollapse::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleAliasUpdate::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::Rule2Comp2Mult::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSub2Add::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleCarryElim::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleBxor2NotEqual::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleLess2Zero::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleLessEqual2Zero::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSLess2Zero::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleEqual2Zero::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleEqual2Constant::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleThreeWayCompare::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleXorCollapse::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleAddMultCollapse::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleCollapseConstants::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleTransformCpool::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePropagateCopy::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleZextEliminate::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSlessToLess::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleZextSless::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleBitUndistribute::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleBooleanUndistribute::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleBooleanDedup::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleBoolZext::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleBooleanNegate::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleLogic2Bool::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSubExtComm::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSubCommute::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleConcatCommute::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleConcatZext::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleZextCommute::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleZextShiftZext::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleShiftAnd::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleConcatZero::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleConcatLeftShift::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSubZext::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSubCancel::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleShiftSub::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleHumptyDumpty::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleDumptyHump::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleHumptyOr::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleNegateIdentity::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSubNormal::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePositiveDiv::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleDivTermAdd::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleDivTermAdd2::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleDivOpt::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSignForm::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSignForm2::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSignDiv2::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleDivChain::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSignNearMult::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleModOpt::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSignMod2nOpt::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSignMod2nOpt2::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSignMod2Opt::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSwitchSingle::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleCondNegate::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleBoolNegate::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleLessEqual::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleLessNotEqual::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleLessOne::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleRangeMeld::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleFloatRange::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePiece2Zext::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePiece2Sext::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePopcountBoolXor::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleXorSwap::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleLzcountShiftBool::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleFloatSign::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleOrCompare::new("analysis")));
        actprop.add_rule(Box::new(crate::subflow::RuleSubvarAnd::new("subvar")));
        actprop.add_rule(Box::new(crate::subflow::RuleSubvarSubpiece::new("subvar")));
        actprop.add_rule(Box::new(crate::subflow::RuleSplitFlow::new("subvar")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePtrFlow::new("subvar", &*conf)));
        actprop.add_rule(Box::new(crate::subflow::RuleSubvarCompZero::new("subvar")));
        actprop.add_rule(Box::new(crate::subflow::RuleSubvarShift::new("subvar")));
        actprop.add_rule(Box::new(crate::subflow::RuleSubvarZext::new("subvar")));
        actprop.add_rule(Box::new(crate::subflow::RuleSubvarSext::new("subvar")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleNegateNegate::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleConditionalMove::new("conditionalexe")));
        actprop.add_rule(Box::new(crate::condexe::RuleOrPredicate::new("conditionalexe")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleFuncPtrEncoding::new("analysis")));
        actprop.add_rule(Box::new(crate::subflow::RuleSubfloatConvert::new("floatprecision")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleFloatCast::new("floatprecision")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleIgnoreNan::new("floatprecision")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleUnsigned2Float::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleInt2FloatCollapse::new("analysis")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePtraddUndo::new("typerecovery")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePtrsubUndo::new("typerecovery")));
        actprop.add_rule(Box::new(crate::ruleaction::RuleSegment::new("segment")));
        actprop.add_rule(Box::new(crate::ruleaction::RulePiecePathology::new("protorecovery")));
        actprop.add_rule(Box::new(crate::double::RuleDoubleLoad::new("doubleload")));
        actprop.add_rule(Box::new(crate::double::RuleDoubleStore::new("doubleprecis")));
        actprop.add_rule(Box::new(crate::double::RuleDoubleIn::new("doubleprecis")));
        actprop.add_rule(Box::new(crate::double::RuleDoubleOut::new("doubleprecis")));
        let extra_rules: Vec<Box<dyn Rule>> = std::mem::take(&mut conf.extra_pool_rules);
        for rule in extra_rules {
            actprop.add_rule(rule);
        }
        actstackstall.add_action(Box::new(actprop));
        actstackstall.add_action(Box::new(crate::coreaction::ActionLaneDivide::new("base")));
        actstackstall.add_action(Box::new(crate::coreaction::ActionMultiCse::new("analysis")));
        actstackstall.add_action(Box::new(crate::coreaction::ActionShadowVar::new("analysis")));
        actstackstall.add_action(Box::new(crate::coreaction::ActionDeindirect::new("deindirect")));
        actstackstall.add_action(Box::new(crate::coreaction::ActionStackPtrFlow::new(
            "stackptrflow",
            stackspace.clone(),
        )));
        actmainloop.add_action(Box::new(actstackstall));
        actmainloop.add_action(Box::new(crate::coreaction::ActionRedundBranch::new("deadcontrolflow")));
        actmainloop.add_action(Box::new(crate::blockaction::ActionBlockStructure::new("blockrecovery")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionConstantPtr::new("typerecovery")));
        let mut actprop2 = ActionPool::new(RULE_REPEATAPPLY, "oppool2");
        actprop2.add_rule(Box::new(crate::ruleaction::RulePushPtr::new("typerecovery")));
        actprop2.add_rule(Box::new(crate::ruleaction::RuleStructOffset0::new("typerecovery")));
        actprop2.add_rule(Box::new(crate::ruleaction::RulePtrArith::new("typerecovery")));
        actprop2.add_rule(Box::new(crate::ruleaction::RuleLoadVarnode::new("stackvars")));
        actprop2.add_rule(Box::new(crate::ruleaction::RuleStoreVarnode::new("stackvars")));
        actmainloop.add_action(Box::new(actprop2));
        actmainloop.add_action(Box::new(crate::coreaction::ActionDeterminedBranch::new("unreachable")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionUnreachable::new("unreachable")));
        actmainloop.add_action(Box::new(crate::blockaction::ActionNodeJoin::new("nodejoin")));
        actmainloop.add_action(Box::new(crate::condexe::ActionConditionalExe::new("conditionalexe")));
        actmainloop.add_action(Box::new(crate::coreaction::ActionConditionalConst::new("analysis")));
        actfullloop.add_action(Box::new(actmainloop));
        actfullloop.add_action(Box::new(crate::coreaction::ActionLikelyTrash::new("protorecovery")));
        actfullloop.add_action(Box::new(crate::coreaction::ActionDirectWrite::new(
            "protorecovery_a",
            true,
        )));
        actfullloop.add_action(Box::new(crate::coreaction::ActionDirectWrite::new(
            "protorecovery_b",
            false,
        )));
        actfullloop.add_action(Box::new(crate::coreaction::ActionDeadCode::new("deadcode")));
        actfullloop.add_action(Box::new(crate::coreaction::ActionDoNothing::new("deadcontrolflow")));
        actfullloop.add_action(Box::new(crate::coreaction::ActionSwitchNorm::new("switchnorm")));
        actfullloop.add_action(Box::new(crate::blockaction::ActionReturnSplit::new("returnsplit")));
        actfullloop.add_action(Box::new(crate::coreaction::ActionUnjustifiedParams::new(
            "protorecovery",
        )));
        actfullloop.add_action(Box::new(crate::coreaction::ActionStartTypes::new("typerecovery")));
        actfullloop.add_action(Box::new(crate::coreaction::ActionActiveReturn::new("protorecovery")));
        act.add_action(Box::new(actfullloop));
        act.add_action(Box::new(crate::coreaction::ActionMappedLocalSync::new("localrecovery")));
        act.add_action(Box::new(crate::coreaction::ActionStartCleanUp::new("cleanup")));
        let mut actcleanup = ActionPool::new(RULE_REPEATAPPLY, "cleanup");
        actcleanup.add_rule(Box::new(crate::ruleaction::RuleMultNegOne::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::ruleaction::RuleAddUnsigned::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::ruleaction::Rule2Comp2Sub::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::subflow::RuleDumptyHumpLate::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::ruleaction::RuleSubRight::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::ruleaction::RuleFloatSignCleanup::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::ruleaction::RuleExpandLoad::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::ruleaction::RulePtrsubCharConstant::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::ruleaction::RuleExtensionPush::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::ruleaction::RulePieceStructure::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::ruleaction::RuleAndStructure::new("cleanup")));
        actcleanup.add_rule(Box::new(crate::subflow::RuleSplitCopy::new("splitcopy")));
        actcleanup.add_rule(Box::new(crate::subflow::RuleSplitLoad::new("splitpointer")));
        actcleanup.add_rule(Box::new(crate::subflow::RuleSplitStore::new("splitpointer")));
        actcleanup.add_rule(Box::new(crate::constseq::RuleStringCopy::new("constsequence")));
        actcleanup.add_rule(Box::new(crate::constseq::RuleStringStore::new("constsequence")));
        actcleanup.add_rule(Box::new(crate::bitfield::RuleBitFieldStore::new("bitfields")));
        actcleanup.add_rule(Box::new(crate::bitfield::RuleBitFieldOut::new("bitfields")));
        actcleanup.add_rule(Box::new(crate::bitfield::RuleBitFieldLoad::new("bitfields")));
        actcleanup.add_rule(Box::new(crate::bitfield::RuleBitFieldIn::new("bitfields")));
        actcleanup.add_rule(Box::new(crate::bitfield::RulePullAbsorb::new("bitfields")));
        actcleanup.add_rule(Box::new(crate::bitfield::RuleInsertAbsorb::new("bitfields")));
        act.add_action(Box::new(actcleanup));
        act.add_action(Box::new(crate::blockaction::ActionPreferComplement::new(
            "blockrecovery",
            true,
        )));
        act.add_action(Box::new(crate::blockaction::ActionStructureTransform::new(
            "blockrecovery",
            true,
        )));
        act.add_action(Box::new(crate::blockaction::ActionNormalizeBranches::new(
            "normalizebranches",
        )));
        act.add_action(Box::new(crate::coreaction::ActionAssignHigh::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionMergeRequired::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionMarkExplicit::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionMarkImplied::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionMergeMultiEntry::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionMergeCopy::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionDominantCopy::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionDynamicSymbols::new("dynamic")));
        act.add_action(Box::new(crate::coreaction::ActionMarkIndirectOnly::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionMergeAdjacent::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionMergeType::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionHideShadow::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionCopyMarker::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionLateDoNothing::new("blockrecovery")));
        act.add_action(Box::new(crate::blockaction::ActionBlockStructure::new("blockrecovery")));
        act.add_action(Box::new(crate::blockaction::ActionPreferComplement::new(
            "blockrecovery",
            false,
        )));
        act.add_action(Box::new(crate::blockaction::ActionStructureTransform::new(
            "blockrecovery",
            false,
        )));
        act.add_action(Box::new(crate::coreaction::ActionOutputPrototype::new("localrecovery")));
        act.add_action(Box::new(crate::coreaction::ActionInputPrototype::new("fixateproto")));
        act.add_action(Box::new(crate::coreaction::ActionMapGlobals::new("fixateglobals")));
        act.add_action(Box::new(crate::coreaction::ActionDynamicSymbols::new("dynamic")));
        act.add_action(Box::new(crate::coreaction::ActionNameVars::new("merge")));
        act.add_action(Box::new(crate::coreaction::ActionSetCasts::new("casts")));
        act.add_action(Box::new(crate::blockaction::ActionFinalStructure::new("blockrecovery")));
        act.add_action(Box::new(crate::coreaction::ActionPrototypeWarnings::new(
            "protorecovery",
        )));
        act.add_action(Box::new(crate::coreaction::ActionStop::new("base")));
        self.register_action(UNIVERSALNAME, Box::new(act));
    }
}
