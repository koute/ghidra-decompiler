use std::fmt::Write;

use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::space::SpaceType;
use crate::varnode::VarnodeId;

fn input_range(data: &Funcdata, op: OpId) -> (i32, i32) {
    let pcode = data.op(op);
    let mut start = 0;
    let mut stop = pcode.num_input();
    match pcode.code() {
        OpCode::Load | OpCode::Store | OpCode::Branch | OpCode::Call => start = 1,
        OpCode::Indirect => stop = 1,
        _ => {}
    }
    (start, stop)
}

fn print_varnode_vertex(data: &mut Funcdata, vn: Option<VarnodeId>, stream: &mut String, glb: &Architecture) {
    let vn = match vn {
        None => return,
        Some(vn) => vn,
    };
    let varnode = data.vn(vn);
    if varnode.is_mark() {
        return;
    }
    let spc = varnode.get_space().expect("varnode without space").clone();
    if spc.get_type() == SpaceType::Fspec {
        return;
    }
    if spc.get_type() == SpaceType::Iop {
        return;
    }
    let _ = write!(stream, "v{} {}", varnode.get_create_index(), spc.get_name());
    stream.push_str(" var ");
    let trans = glb.translate.as_deref().expect("architecture without translator");
    varnode.print_raw_no_markup(stream, trans, data);
    match varnode.get_def() {
        Some(op) => {
            let _ = write!(stream, " {:x}", data.op(op).get_addr().get_offset());
        }
        None => {
            if varnode.is_input() {
                stream.push_str(" i");
            } else {
                stream.push_str(" <na>");
            }
        }
    }
    stream.push('\n');
    data.vn_mut(vn).set_mark();
}

fn print_op_vertex(data: &Funcdata, op: OpId, stream: &mut String, glb: &Architecture) {
    let pcode = data.op(op);
    let _ = write!(stream, "o{} ", pcode.get_time());
    if pcode.is_branch() {
        stream.push_str("branch");
    } else if pcode.is_call() {
        stream.push_str("call");
    } else if pcode.is_marker() {
        stream.push_str("marker");
    } else {
        stream.push_str("basic");
    }
    stream.push_str(" op ");
    let name = data.op_get_op_name(op, glb);
    if !name.is_empty() {
        stream.push_str(name);
    } else {
        stream.push_str("unkop");
    }
    let _ = writeln!(stream, " {:x}", pcode.get_addr().get_offset());
}

fn dump_varnode_vertex(data: &mut Funcdata, stream: &mut String, glb: &Architecture) {
    stream.push_str("\n\n// Add Vertices\n");
    stream.push_str("*CMD=*COLUMNAR_INPUT,\n");
    stream.push_str("  Command=AddVertices,\n");
    stream.push_str("  Parsing=WhiteSpace,\n");
    stream.push_str("  Fields=({Name=Internal, Location=1},\n");
    stream.push_str("          {Name=SubClass, Location=2},\n");
    stream.push_str("          {Name=Type, Location=3},\n");
    stream.push_str("          {Name=Name, Location=4},\n");
    stream.push_str("          {Name=Address, Location=5});\n\n");
    stream.push_str("//START:varnodes\n");
    let alive = data.obank.alive_ops();
    for op in alive.iter() {
        let out = data.op(*op).get_out();
        print_varnode_vertex(data, out, stream, glb);
        let (start, stop) = input_range(data, *op);
        for slot in start..stop {
            let vn = data.op(*op).get_in(slot);
            print_varnode_vertex(data, Some(vn), stream, glb);
        }
    }
    stream.push_str("*END_COLUMNS\n");
    for op in alive.iter() {
        if let Some(out) = data.op(*op).get_out() {
            data.vn_mut(out).clear_mark();
        }
        for slot in 0..data.op(*op).num_input() {
            let vn = data.op(*op).get_in(slot);
            data.vn_mut(vn).clear_mark();
        }
    }
}

fn dump_op_vertex(data: &mut Funcdata, stream: &mut String, glb: &Architecture) {
    stream.push_str("\n\n// Add Vertices\n");
    stream.push_str("*CMD=*COLUMNAR_INPUT,\n");
    stream.push_str("  Command=AddVertices,\n");
    stream.push_str("  Parsing=WhiteSpace,\n");
    stream.push_str("  Fields=({Name=Internal, Location=1},\n");
    stream.push_str("          {Name=SubClass, Location=2},\n");
    stream.push_str("          {Name=Type, Location=3},\n");
    stream.push_str("          {Name=Name, Location=4},\n");
    stream.push_str("          {Name=Address, Location=5});\n\n");
    stream.push_str("//START:opnodes\n");
    for op in data.obank.alive_ops() {
        print_op_vertex(data, op, stream, glb);
    }
    stream.push_str("*END_COLUMNS\n");
}

fn print_edges(data: &Funcdata, op: OpId, stream: &mut String) {
    let pcode = data.op(op);
    if let Some(vn) = pcode.get_out() {
        let _ = writeln!(
            stream,
            "o{} v{} output",
            pcode.get_time(),
            data.vn(vn).get_create_index()
        );
    }
    let (start, stop) = input_range(data, op);
    for slot in start..stop {
        let vn = data.vn(pcode.get_in(slot));
        let tp = vn.get_space().expect("varnode without space").get_type();
        if tp != SpaceType::Fspec && tp != SpaceType::Iop {
            let _ = writeln!(stream, "v{} o{} input", vn.get_create_index(), pcode.get_time());
        }
    }
}

fn dump_edges(data: &mut Funcdata, stream: &mut String) {
    stream.push_str("\n\n// Add Edges\n");
    stream.push_str("*CMD=*COLUMNAR_INPUT,\n");
    stream.push_str("  Command=AddEdges,\n");
    stream.push_str("  Parsing=WhiteSpace,\n");
    stream.push_str("  Fields=({Name=*FromKey, Location=1},\n");
    stream.push_str("          {Name=*ToKey, Location=2},\n");
    stream.push_str("          {Name=Name, Location=3});\n\n");
    stream.push_str("//START:edges\n");
    for op in data.obank.alive_ops() {
        print_edges(data, op, stream);
    }
    stream.push_str("*END_COLUMNS\n");
}

pub fn dump_dataflow_graph(data: &mut Funcdata, stream: &mut String, glb: &Architecture) {
    let name = data.get_name().to_string();
    let _ = writeln!(stream, "*CMD=NewGraphWindow, WindowName={}-dataflow;", name);
    let _ = writeln!(stream, "*CMD=*NEXUS,Name={}-dataflow;", name);
    stream.push_str("\n// AutomaticArrangement\n");
    stream.push_str("  *CMD = AlterLocalPreferences, Name = AutomaticArrangement,\n");
    stream.push_str("  ~ReplaceAllParams = TRUE,\n");
    stream.push_str("  EnableAutomaticArrangement=true,\n");
    stream.push_str("  OnlyActOnVerticesWithoutCoordsIfOff=false,\n");
    stream.push_str("  DontUpdateMediumWithUserArrangement=false,\n");
    stream.push_str("  UserAddedArrangmentParams=({ServiceName=SimpleHierarchyFromSources,ServiceParams={~SkipPromptForParams=true}}),\n");
    stream.push_str("  SmallSize=50,\n");
    stream.push_str("  DontUpdateLargeWithUserArrangement=true,\n");
    stream.push_str("  NewVertexActionIfOff=ArrangeByMDS,\n");
    stream.push_str("  MediumSizeArrangement=SimpleHierarchyFromSources,\n");
    stream.push_str("  SmallSizeArrangement=SimpleHierarchyFromSources,\n");
    stream.push_str("  MediumSize=800,\n");
    stream.push_str("  LargeSizeArrangement=ArrangeInCircle,\n");
    stream.push_str("  DontUpdateSmallWithUserArrangement=false,\n");
    stream.push_str("  ActionSizeGainIfOff=1.0;\n");
    stream.push_str("\n// VertexColors\n");
    stream.push_str("  *CMD = AlterLocalPreferences, Name = VertexColors,\n");
    stream.push_str("  ~ReplaceAllParams = TRUE,\n");
    stream.push_str("  Mapping=({DisplayChoice=Magenta,AttributeValue=branch},\n");
    stream.push_str("  {DisplayChoice=Blue,AttributeValue=register},\n");
    stream.push_str("  {DisplayChoice=Black,AttributeValue=unique},\n");
    stream.push_str("  {DisplayChoice=DarkGreen,AttributeValue=const},\n");
    stream.push_str("  {DisplayChoice=DarkOrange,AttributeValue=ram},\n");
    stream.push_str("  {DisplayChoice=Orange,AttributeValue=stack}),\n");
    stream.push_str("  ChoiceForValueNotCovered=Red,\n");
    stream.push_str("  Extraction=CompleteValue,\n");
    stream.push_str("  ExtractionParams={},\n");
    stream.push_str("  AttributeName=SubClass,\n");
    stream.push_str("  ChoiceForMissingValue=Red,\n");
    stream.push_str("  CanOverride=true,\n");
    stream.push_str("  OverrideAttributeName=Color,\n");
    stream.push_str("  UsingRange=false;\n");
    stream.push_str("\n//     VertexIcons\n");
    stream.push_str("  *CMD = AlterLocalPreferences, Name = VertexIcons,\n");
    stream.push_str("  ~ReplaceAllParams = TRUE,\n");
    stream.push_str("  Mapping=({DisplayChoice=Circle,AttributeValue=var},\n");
    stream.push_str("  {DisplayChoice=Square,AttributeValue=op}),\n");
    stream.push_str("  ChoiceForValueNotCovered=Circle,\n");
    stream.push_str("  Extraction=CompleteValue,\n");
    stream.push_str("  ExtractionParams={},\n");
    stream.push_str("  AttributeName=Type,\n");
    stream.push_str("  ChoiceForMissingValue=Circle,\n");
    stream.push_str("  CanOverride=true,\n");
    stream.push_str("  OverrideAttributeName=Icon,\n");
    stream.push_str("  UsingRange=false;\n");
    stream.push_str("\n//     VertexLabels\n");
    stream.push_str("  *CMD = AlterLocalPreferences, Name = VertexLabels,\n");
    stream.push_str("  ~ReplaceAllParams = TRUE,\n");
    stream.push_str("  Center=({SpecialColor=Black,SpecialFontName=SansSerif,Format=StandardFormat,UseSpecialFontName=false,LabelAlignment=Center,TreatBackSlashNAsNewLine=false,MaxLines=4,FontSize=10,IncludeBackground=false,SqueezeLinesTogether=true,BackgroundColor=Black,UseSpecialColor=false,AttributeName=Name,MaxWidth=100}),\n");
    stream.push_str("  East=(),\n");
    stream.push_str("  SouthEast=(),\n");
    stream.push_str("  North=(),\n");
    stream.push_str("  West=(),\n");
    stream.push_str("  SouthWest=(),\n");
    stream.push_str("  NorthEast=(),\n");
    stream.push_str("  South=(),\n");
    stream.push_str("  NorthWest=();\n");
    stream.push_str("\n// Attributes\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=SubClass,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=Type,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=Internal,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=Name,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=Address,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=Name,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Edges;\n\n");
    stream.push_str("*CMD=SetKeyAttribute,\n");
    stream.push_str("        Category=Vertices,");
    stream.push_str("        Name=Internal;\n\n");
    dump_varnode_vertex(data, stream, glb);
    dump_op_vertex(data, stream, glb);
    dump_edges(data, stream);
}

fn print_block_vertex(data: &Funcdata, bl: BlockId, stream: &mut String) {
    let block = data.block(bl);
    let _ = write!(stream, " {}", block.size_out());
    let _ = write!(stream, " {}", block.size_in());
    let _ = write!(stream, " {}", block.get_index());
    let _ = write!(stream, " {:x}", block.get_start().get_offset());
    let _ = writeln!(stream, " {:x}", block.get_stop().get_offset());
}

fn print_block_edge(data: &Funcdata, bl: BlockId, stream: &mut String) {
    let block = data.block(bl);
    for slot in 0..block.size_in() {
        let _ = writeln!(
            stream,
            "{} {}",
            data.block(block.get_in(slot)).get_index(),
            block.get_index()
        );
    }
}

fn dump_block_vertex(data: &Funcdata, graph: BlockId, stream: &mut String, falsenode: bool) {
    stream.push_str("\n\n// Add Vertices\n");
    stream.push_str("*CMD=*COLUMNAR_INPUT,\n");
    stream.push_str("  Command=AddVertices,\n");
    stream.push_str("  Parsing=WhiteSpace,\n");
    stream.push_str("  Fields=({Name=SizeOut, Location=1},\n");
    stream.push_str("          {Name=SizeIn, Location=2},\n");
    stream.push_str("          {Name=Internal, Location=3},\n");
    stream.push_str("          {Name=Index, Location=4},\n");
    stream.push_str("          {Name=Start, Location=5},\n");
    stream.push_str("          {Name=Stop, Location=6});\n\n");
    if falsenode {
        stream.push_str("-1 0 0 -1 0 0\n");
    }
    for bl in data.block(graph).get_list().iter() {
        print_block_vertex(data, *bl, stream);
    }
    stream.push_str("*END_COLUMNS\n");
}

fn dump_block_edges(data: &Funcdata, graph: BlockId, stream: &mut String) {
    stream.push_str("\n\n// Add Edges\n");
    stream.push_str("*CMD=*COLUMNAR_INPUT,\n");
    stream.push_str("  Command=AddEdges,\n");
    stream.push_str("  Parsing=WhiteSpace,\n");
    stream.push_str("  Fields=({Name=*FromKey, Location=1},\n");
    stream.push_str("          {Name=*ToKey, Location=2});\n\n");
    for bl in data.block(graph).get_list().iter() {
        print_block_edge(data, *bl, stream);
    }
    stream.push_str("*END_COLUMNS\n");
}

fn print_dom_edge(data: &Funcdata, bl: BlockId, stream: &mut String, falsenode: bool) {
    let block = data.block(bl);
    match block.get_immed_dom() {
        Some(dom) => {
            let _ = writeln!(stream, "{} {}", data.block(dom).get_index(), block.get_index());
        }
        None => {
            if falsenode {
                let _ = writeln!(stream, "-1 {}", block.get_index());
            }
        }
    }
}

fn dump_dom_edges(data: &Funcdata, graph: BlockId, stream: &mut String, falsenode: bool) {
    stream.push_str("\n\n// Add Edges\n");
    stream.push_str("*CMD=*COLUMNAR_INPUT,\n");
    stream.push_str("  Command=AddEdges,\n");
    stream.push_str("  Parsing=WhiteSpace,\n");
    stream.push_str("  Fields=({Name=*FromKey, Location=1},\n");
    stream.push_str("          {Name=*ToKey, Location=2});\n\n");
    for bl in data.block(graph).get_list().iter() {
        print_dom_edge(data, *bl, stream, falsenode);
    }
    stream.push_str("*END_COLUMNS\n");
}

fn dump_block_attributes(stream: &mut String) {
    stream.push_str("\n// Attributes\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=SizeOut,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=SizeIn,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=Internal,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=Index,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=Start,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=DefineAttribute,\n");
    stream.push_str("        Name=Stop,\n");
    stream.push_str("        Type=String,\n");
    stream.push_str("        Category=Vertices;\n\n");
    stream.push_str("*CMD=SetKeyAttribute,\n");
    stream.push_str("        Category=Vertices,");
    stream.push_str("        Name=Index;\n\n");
}

fn dump_block_properties(stream: &mut String) {
    stream.push_str("\n// AutomaticArrangement\n");
    stream.push_str("  *CMD = AlterLocalPreferences, Name = AutomaticArrangement,\n");
    stream.push_str("  ~ReplaceAllParams = TRUE,\n");
    stream.push_str("  EnableAutomaticArrangement=true,\n");
    stream.push_str("  OnlyActOnVerticesWithoutCoordsIfOff=false,\n");
    stream.push_str("  DontUpdateMediumWithUserArrangement=false,\n");
    stream.push_str("  UserAddedArrangmentParams=({ServiceName=SimpleHierarchyFromSources,ServiceParams={~SkipPromptForParams=true}}),\n");
    stream.push_str("  SmallSize=50,\n");
    stream.push_str("  DontUpdateLargeWithUserArrangement=true,\n");
    stream.push_str("  NewVertexActionIfOff=ArrangeByMDS,\n");
    stream.push_str("  MediumSizeArrangement=SimpleHierarchyFromSources,\n");
    stream.push_str("  SmallSizeArrangement=SimpleHierarchyFromSources,\n");
    stream.push_str("  MediumSize=800,\n");
    stream.push_str("  LargeSizeArrangement=ArrangeInCircle,\n");
    stream.push_str("  DontUpdateSmallWithUserArrangement=false,\n");
    stream.push_str("  ActionSizeGainIfOff=1.0;\n");
    stream.push_str("\n// VertexColors\n");
    stream.push_str("  *CMD = AlterLocalPreferences, Name = VertexColors,\n");
    stream.push_str("  ~ReplaceAllParams = TRUE,\n");
    stream.push_str("  Mapping=({DisplayChoice=Red,AttributeValue=0},\n");
    stream.push_str("  {DisplayChoice=Blue,AttributeValue=1},\n");
    stream.push_str("  {DisplayChoice=Yellow,AttributeValue=2}),\n");
    stream.push_str("  ChoiceForValueNotCovered=Purple,\n");
    stream.push_str("  Extraction=CompleteValue,\n");
    stream.push_str("  ExtractionParams={},\n");
    stream.push_str("  AttributeName=SizeOut,\n");
    stream.push_str("  ChoiceForMissingValue=Purple,\n");
    stream.push_str("  CanOverride=true,\n");
    stream.push_str("  OverrideAttributeName=Color,\n");
    stream.push_str("  UsingRange=false;\n");
    stream.push_str("\n//     VertexIcons\n");
    stream.push_str("  *CMD = AlterLocalPreferences, Name = VertexIcons,\n");
    stream.push_str("  ~ReplaceAllParams = TRUE,\n");
    stream.push_str("  Mapping=({DisplayChoice=Square,AttributeValue=0}),\n");
    stream.push_str("  ChoiceForValueNotCovered=Circle,\n");
    stream.push_str("  Extraction=CompleteValue,\n");
    stream.push_str("  ExtractionParams={},\n");
    stream.push_str("  AttributeName=SizeIn,\n");
    stream.push_str("  ChoiceForMissingValue=Circle,\n");
    stream.push_str("  CanOverride=true,\n");
    stream.push_str("  OverrideAttributeName=Icon,\n");
    stream.push_str("  UsingRange=false;\n");
    stream.push_str("\n//     VertexLabels\n");
    stream.push_str("  *CMD = AlterLocalPreferences, Name = VertexLabels,\n");
    stream.push_str("  ~ReplaceAllParams = TRUE,\n");
    stream.push_str("  Center=({MaxLines=4,SqueezeLinesTogether=true,TreatBackSlashNAsNewLine=false,FontSize=10,Format=StandardFormat,IncludeBackground=false,BackgroundColor=Black,AttributeName=Start,UseSpecialFontName=false,SpecialColor=Black,SpecialFontName=SansSerif,UseSpecialColor=false,LabelAlignment=Center,MaxWidth=100}),\n");
    stream.push_str("  East=(),\n");
    stream.push_str("  SouthEast=(),\n");
    stream.push_str("  North=(),\n");
    stream.push_str("  West=(),\n");
    stream.push_str("  SouthWest=(),\n");
    stream.push_str("  NorthEast=(),\n");
    stream.push_str("  South=(),\n");
    stream.push_str("  NorthWest=();\n");
}

pub fn dump_controlflow_graph(name: &str, data: &Funcdata, graph: BlockId, stream: &mut String) {
    let _ = writeln!(stream, "*CMD=NewGraphWindow, WindowName={}-controlflow;", name);
    let _ = writeln!(stream, "*CMD=*NEXUS,Name={}-controlflow;", name);
    dump_block_properties(stream);
    dump_block_attributes(stream);
    dump_block_vertex(data, graph, stream, false);
    dump_block_edges(data, graph, stream);
}

pub fn dump_dom_graph(name: &str, data: &Funcdata, graph: BlockId, stream: &mut String) {
    let count = data
        .block(graph)
        .get_list()
        .iter()
        .filter(|bl| data.block(**bl).get_immed_dom().is_none())
        .count();
    let falsenode = count > 1;
    let _ = writeln!(stream, "*CMD=NewGraphWindow, WindowName={}-dom;", name);
    let _ = writeln!(stream, "*CMD=*NEXUS,Name={}-dom;", name);
    dump_block_properties(stream);
    dump_block_attributes(stream);
    dump_block_vertex(data, graph, stream, falsenode);
    dump_dom_edges(data, graph, stream, falsenode);
}
