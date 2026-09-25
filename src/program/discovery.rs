use std::collections::BTreeSet;
use std::ops::Range;

use super::{FunctionSource, Program};
use crate::address::Address;
use crate::database::SymbolId;
use crate::error::Result;
use crate::op::PcodeOp;
use crate::oplist::LinkedNode;
use crate::space::SpaceRef;

pub(super) struct FlowFacts {
    pub(super) call_targets: Vec<u64>,
    pub(super) constants: BTreeSet<u64>,
    pub(super) body: Range<u64>,
}

impl Program {
    pub(super) fn flow_facts(&mut self, sym: SymbolId) -> Result<Option<FlowFacts>> {
        self.architecture.with_function(sym, |function, architecture| {
            if function.has_no_code() {
                return Ok(None);
            }
            architecture.clear_analysis(function);
            let space: Option<SpaceRef> = function.get_address().get_space().cloned();
            let highest = space.as_ref().map(|space| space.get_highest()).unwrap_or(u64::MAX);
            let start = Address::from_parts(space.clone(), 0);
            let end = Address::from_parts(space, highest);
            if function.follow_flow(&start, &end, architecture).is_err() {
                architecture.clear_analysis(function);
                return Ok(None);
            }
            let entry = function.get_address().get_offset();
            let mut facts = FlowFacts {
                call_targets: Vec::new(),
                constants: BTreeSet::new(),
                body: entry..entry + 1,
            };
            let mut position = function.begin_op_alive();
            while let Some(op) = position {
                let operation = function.op(op);
                let address = operation.get_addr().get_offset();
                facts.body = facts.body.start.min(address)..facts.body.end.max(address + 1);
                for slot in 0..operation.num_input() {
                    let input = function.vn(operation.get_in(slot));
                    if input.is_constant() {
                        facts.constants.insert(input.get_offset());
                    }
                }
                position = operation.links(PcodeOp::INSERT_LIST).next;
            }
            for index in 0..function.num_calls() {
                let target = function.call_spec(function.get_call_specs(index)).get_entry_address();
                if !target.is_invalid() {
                    facts.call_targets.push(target.get_offset());
                }
            }
            architecture.clear_analysis(function);
            Ok(Some(facts))
        })
    }

    pub fn discover_functions(&mut self) -> Result<()> {
        let has_function_symbols = self.functions.values().any(|record| {
            matches!(
                record.source,
                FunctionSource::SymbolTable | FunctionSource::DynamicSymbol
            )
        });
        let Some(entry) = self.entry.take().filter(|_| !has_function_symbols) else {
            return Ok(());
        };
        super::panic_guard(|| self.discover_from(entry))
    }

    fn discover_from(&mut self, entry: u64) -> Result<()> {
        let mut pending = vec![entry];
        let mut visited = BTreeSet::new();
        while let Some(address) = pending.pop() {
            if !visited.insert(address) || !self.is_code_address(address) {
                continue;
            }
            let sym = self.discovered_function(address)?;
            let Some(facts) = self.flow_facts(sym)? else {
                continue;
            };
            pending.extend(facts.call_targets);
            pending.extend(
                facts
                    .constants
                    .into_iter()
                    .filter(|constant| !facts.body.contains(constant)),
            );
        }
        Ok(())
    }

    fn discovered_function(&mut self, address: u64) -> Result<SymbolId> {
        let code_address = self.code_address(address)?;
        let scope = self.global_scope()?;
        if let Some(sym) = self.symbol_table()?.scope_query_function(scope, &code_address) {
            return Ok(sym);
        }
        let mut name = String::new();
        self.architecture.name_function(&code_address, &mut name);
        self.add_named_function(&name, None, &code_address, FunctionSource::Discovered)
    }
}
