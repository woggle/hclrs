use ast::{Statement, WireDecl, WireWidth, WireValue, WireValues, SpannedExpr};
use ast::{Statement, WireDecl, WireWidth, WireValue, WireValues, SpannedExpr,Expr,BinOpCode, UnOpCode};
use errors::{find_close_names_in, Error};
use lexer::Span;
use y86_disasm::{disassemble_to_string, name_register};
use std::collections::hash_set::HashSet;
use std::collections::hash_map::HashMap;
use std::collections::btree_map::BTreeMap;
use std::collections::VecDeque;
use std::cmp::max;
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::io::{BufRead, Write, sink};

struct Graph<T> {
    edges: HashMap<T, HashSet<T>>,
    edges_inverted: HashMap<T, HashSet<T>>,
    nodes: HashSet<T>,
    num_edges: usize,
}

impl<T: PartialEq + Eq + Hash + Clone + Debug> Graph<T> {
    fn add_node(&mut self, node: T) {
        self.nodes.insert(node);
    }

    fn insert(&mut self, from: T, to: T) {
        debug!("insert node {:?} / {:?}", from, to);
        self.add_node(from.clone());
        self.add_node(to.clone());
        let for_node = self.edges.entry(from.clone()).or_insert_with(|| HashSet::new());
        (*for_node).insert(to.clone());
        let inverted_for_node = self.edges_inverted.entry(to).or_insert_with(|| HashSet::new());
        (*inverted_for_node).insert(from);
        self.num_edges = self.num_edges + 1;
    }

    fn contains_node(&self, node: &T) -> bool {
        return self.nodes.contains(&node);
    }

    #[cfg(test)]
    fn contains_edge(&self, from: &T, to: &T) -> bool {
        match self.edges.get(&from) {
            Some(set) => set.contains(&to),
            None => false,
        }
    }

    fn out_edges(&self, to: &T) -> HashSet<T> {
        if let Some(result) = self.edges.get(to) {
            result.clone()
        } else {
            HashSet::new()
        }
    }

    fn find_cycle(&self) -> Vec<T> {
        let mut stack: VecDeque<(Option<T>, T)> = VecDeque::new();
        let mut parents: HashMap<T, Option<T>> = HashMap::new();
        for node in &self.nodes {
            stack.push_back((None, node.clone()));
        }
        while let Some((maybe_parent, cur)) = stack.pop_front() {
            debug!("queue {:?}; processing {:?}->{:?}", stack, maybe_parent, cur);
            if parents.get(&cur).is_none() {
                for out in &self.out_edges(&cur) {
                    debug!("enqueue {:?} from {:?}", out, cur);
                    stack.push_front((Some(cur.clone()), out.clone()));
                }
            }
            let mut found_other_parent = false;
            if let Some(ref parent) = maybe_parent {
                if parents.contains_key(&cur) {
                    found_other_parent = true;
                    // see if this was a back-edge
                    debug!("checking for backwards edge to {:?} via {:?}", cur, parent);
                    let mut back_path = vec!(parent.clone());
                    while *back_path.last().unwrap() != cur {
                        if let Some(&Some(ref grandparent)) = parents.get(back_path.last().unwrap()) {
                            back_path.push(grandparent.clone());
                        } else {
                            break;
                        }
                    }
                    // back_path is parent <- ... <- cur and there is an edge
                    // cur <- parent
                    if *back_path.last().unwrap() == cur {
                        let mut forward_path = back_path;
                        forward_path.reverse();
                        return forward_path;
                    }
                }
            }
            if !found_other_parent {
                parents.insert(cur.clone(), maybe_parent.clone());
                debug!("parent set for {:?}", cur);
            }
            assert!(parents.get(&cur).is_some());
        }
        panic!("find_cycle() called when no cycle present");
    }

    // topological sort, or find cycle
    fn topological_sort(&self) -> Result<Vec<T>, Vec<T>> {
        let mut result = Vec::new();

        // Step 1: Queue nodes with no incoming edges
        let mut queue = VecDeque::new();
        let mut num_in_unvisited = HashMap::new();
        for node in &self.nodes {
            if !self.edges_inverted.contains_key(&node) {
                debug!("found starting node {:?}", node);
                queue.push_front(node.clone());
            }
            num_in_unvisited.insert(node.clone(),
                self.edges_inverted.get(&node).map_or(0, |x| x.len())
            );
        }

        debug!("Initial queue: {:?}", queue);
        debug!("Initial in counts: {:?}", num_in_unvisited);

        let mut visited = HashSet::new();
        while let Some(cur) = queue.pop_back() {
            debug!("Process {:?} from queue", cur);
            result.push(cur.clone());
            if let Some(out_edges) = self.edges.get(&cur) {
                for out_node in out_edges {
                    let pair = (cur.clone(), out_node.clone());
                    debug!("Found edge {:?}", pair);
                    if !visited.contains(&pair) {
                        visited.insert(pair);
                        let new_in_unvisited = num_in_unvisited.get(out_node).unwrap_or(&0) - 1;
                        num_in_unvisited.insert(out_node.clone(), new_in_unvisited);
                        if new_in_unvisited == 0 {
                            debug!("Now enqueue {:?}", out_node);
                            queue.push_front(out_node.clone());
                        }
                    }
                }
            }
        }

        if visited.len() != self.num_edges {
            return Err(self.find_cycle());
        }

        Ok(result)
    }

    fn new() -> Graph<T> {
        Graph {
            edges: HashMap::new(),
            edges_inverted: HashMap::new(),
            nodes: HashSet::new(),
            num_edges: 0,
        }
    }
}

#[derive(Debug,PartialEq,Eq,Clone)]
pub enum Action {
    // not included:
        // register bank processing (done at beginning of cycle)
    Assign(String, SpannedExpr, WireWidth),
    ReadProgramRegister { number: String, out_port: String },
    ReadMemory { is_read: Option<String>, address: String, out_port: String, bytes: u8, is_instruction: bool, },
    // these actions MUST be done last:
    WriteProgramRegister { number: String, in_port: String },
    WriteMemory { is_write: Option<String>, address: String, in_port: String, bytes: u8 },
    SetStatus { in_wire: String },
}

// psuedo-assignment for fixed functionality
#[derive(Debug)]
pub struct FixedFunction {
    in_wires: Vec<WireDecl>,
    out_wire: Option<WireDecl>,
    action: Action,
    mandatory: bool,
}

impl FixedFunction {
    fn read_port(number: &str, output: &str) -> FixedFunction {
        FixedFunction {
            in_wires: vec!(WireDecl::synthetic(number, 4)),
            out_wire: Some(WireDecl::synthetic(output, 64)),
            action: Action::ReadProgramRegister {
                number: String::from(number),
                out_port: String::from(output),
            },
            mandatory: false,
        }
    }

    fn write_port(number: &str, input: &str) -> FixedFunction {
        FixedFunction {
            in_wires: vec!(
                WireDecl::synthetic(number, 4),
                WireDecl::synthetic(input, 64)
            ),
            out_wire: None,
            action: Action::WriteProgramRegister {
                number: String::from(number),
                in_port: String::from(input),
            },
            mandatory: false,
        }
    }
}

pub fn y86_fixed_functions() -> Vec<FixedFunction> {
    return vec!(
        FixedFunction {
            in_wires: vec!(WireDecl::synthetic("Stat", 3)),
            out_wire: None,
            action: Action::SetStatus { in_wire: String::from("Stat") },
            mandatory: true,
        },
        FixedFunction {
            in_wires: vec!(WireDecl::synthetic("pc", 64)),
            out_wire: Some(WireDecl::synthetic("i10bytes", 80)),
            action: Action::ReadMemory {
                is_read: None,
                address: String::from("pc"),
                out_port: String::from("i10bytes"),
                bytes: 10,
                is_instruction: true,
            },
            mandatory: true,
        },
        FixedFunction {
            in_wires: vec!(
                WireDecl::synthetic("mem_addr", 64),
                WireDecl::synthetic("mem_readbit", 1)
            ),
            out_wire: Some(WireDecl::synthetic("mem_output", 64)),
            action: Action::ReadMemory {
                is_read: Some(String::from("mem_readbit")),
                address: String::from("mem_addr"),
                out_port: String::from("mem_output"),
                bytes: 8,
                is_instruction: false,
            },
            mandatory: false,
        },
        FixedFunction {
            in_wires: vec!(
                WireDecl::synthetic("mem_addr", 64),
                WireDecl::synthetic("mem_input", 64),
                WireDecl::synthetic("mem_writebit", 1)
            ),
            out_wire: None,
            action: Action::WriteMemory {
                is_write: Some(String::from("mem_writebit")),
                address: String::from("mem_addr"),
                in_port: String::from("mem_input"),
                bytes: 8,
            },
            mandatory: false,
        },
        FixedFunction::read_port("reg_srcA", "reg_outputA"),
        FixedFunction::read_port("reg_srcB", "reg_outputB"),
        // note: the order here is important for priority
        FixedFunction::write_port("reg_dstE", "reg_inputE"),
        FixedFunction::write_port("reg_dstM", "reg_inputM"),
    )
}

#[derive(Debug,Clone)]
pub struct RegisterBank {
    label: String,
    signals: Vec<(String, String, WireWidth)>, // in, out
    defaults: WireValues, // mapped to out names
    stall_signal: String,
    bubble_signal: String,
}
impl RegisterBank {
    pub fn get_signal(&self) -> Vec<(String, String, WireWidth)> {
        return self.signals.clone()
    }
    pub fn get_label(&self) -> String {
            return self.label.clone()
        }

}

// interpreter representation of a program
#[derive(Debug,Clone)]
pub struct Program {
    constants: WireValues,
    actions: Vec<Action>,  // in topological order
    register_banks: Vec<RegisterBank>,

    // wires which exist, but only ever have a default
    // value and should not be displayed in debugging output
    defaulted_wires: HashSet<String>,
}


fn resolve_constants(exprs: &HashMap<&str, &SpannedExpr>) -> Result<HashMap<String, WireValue>, Error> {
    debug!("resolve constants");
    let mut errors = Vec::new();
    let mut graph = Graph::new();
    for (name, expr) in exprs {
        for in_name in expr.referenced_wires() {
            graph.insert(in_name, name);
        }
        graph.add_node(name);
    }
    if errors.len() > 0 {
        return Err(Error::MultipleErrors(errors));
    }
    match graph.topological_sort() {
        Ok(sorted) => {
            let mut results = HashMap::new();
            for name in sorted {
                match exprs.get(&name).unwrap().evaluate(&results) {
                    Ok(value) => {
                        results.insert(
                            String::from(name),
                            value
                        );
                    },
                    Err(e) => { 
                        errors.push(e);
                    },
                }
            }
            if errors.len() > 0 {
                return Err(Error::MultipleErrors(errors));
            }
            debug!("done resolve constants");
            Ok(results)
        },
        Err(cycle) => {
            return Err(Error::WireLoop(cycle.into_iter().map(String::from).collect()));
        }
    }
}

fn assignments_to_actions<'a>(
        assignments: &'a HashMap<&'a str, &SpannedExpr>,
        widths: &'a HashMap<&'a str, WireWidth>,
        known_values: &'a HashSet<&'a str>,
        fixed_functions: &'a Vec<FixedFunction>,
        wire_decl_spans: &'a HashMap<&'a str, Span>,
        assign_spans: &'a HashMap<&'a str, Span>,
        constants: &'a WireValues,
    ) -> Result<Vec<Action>, Error> {
    let mut fixed_by_output = HashMap::new();
    let mut fixed_no_output = Vec::new();
    let mut graph = Graph::new();
    for (name, expr) in assignments {
        graph.add_node(*name);
        for in_name in expr.referenced_wires() {
            if !known_values.contains(in_name) {
                graph.insert(in_name, name);
            }
        }
    }

    let mut unused_fixed_inputs = HashSet::new();
    let mut used_fixed_inputs = HashSet::new();
    for fixed in fixed_functions.iter() {
        let mut missing_inputs: Vec<&str> = Vec::new();
        for in_name in &fixed.in_wires {
            if known_values.contains(in_name.name.as_str()) {
                panic!("unexpected duplicate definition of {}", in_name.name.as_str());
            }
            if !assignments.contains_key(in_name.name.as_str()) {
                missing_inputs.push(in_name.name.as_str());
            }
        }
        if fixed.mandatory && missing_inputs.len() > 0 {
            let missing_list = missing_inputs.iter().map(|x| Error::UnsetBuiltinWire(String::from(*x))).collect();
            return Err(Error::MultipleErrors(missing_list));
        } else if missing_inputs.len() > 0 {
            if let Some(ref decl) = fixed.out_wire {
                if graph.contains_node(&decl.name.as_str()) {
                    let missing_list = missing_inputs.iter().map(|x| Error::UnsetBuiltinWire(String::from(*x))).collect();
                    return Err(Error::MultipleErrors(missing_list));
                }
            }
            if missing_inputs.len() != fixed.in_wires.len() {
                for in_name in &fixed.in_wires {
                    if assignments.contains_key(in_name.name.as_str()) {
                        unused_fixed_inputs.insert(in_name.name.as_str());
                    }
                }
            }
            debug!("not initializing {:?} due to missing inputs", fixed);
            continue;
        }
        match fixed.out_wire {
            None => {
                fixed_no_output.push(fixed);
            },
            Some(ref decl) => {
                if known_values.contains(decl.name.as_str()) ||
                   assignments.contains_key(decl.name.as_str()) {
                    panic!("unexpected duplicate definition of {}", decl.name);
                }
                fixed_by_output.insert(decl.name.as_str(), fixed);
                for in_name in &fixed.in_wires {
                    used_fixed_inputs.insert(in_name.name.as_str());
                    graph.insert(in_name.name.as_str(), decl.name.as_str());
                }
            }
        }
    }

    // if any piece of fixed functionality was not created because some but not all of its
    // inputs exist, trigger an error unless all those inputs are used by other fixed
    // functionality.

    // this makes doing something like setting reg_dstE without setting reg_inputE an error,
    // but doesn't make something like setting mem_addr without mem_writebit an error
    {
        let mut bad_inputs = Vec::new();
        for name in unused_fixed_inputs {
            if !used_fixed_inputs.contains(name) {
                bad_inputs.push(name);
            }
        }

        if bad_inputs.len() > 0 {
            let mut errors = Vec::new();
            for bad_input in bad_inputs {
                let mut matching_fixed: Vec<Vec<String>> = Vec::new();
                for fixed in fixed_functions.iter() {
                    if fixed.in_wires.iter().find(|x| x.name == bad_input).is_some() {
                        matching_fixed.push(
                            fixed.in_wires.iter().map(|x| x.name.clone()).collect()
                        )
                    }
                }
                errors.push(Error::PartialFixedInput {
                    found_input: String::from(bad_input),
                    all_inputs: matching_fixed,
                });
            }
            return Err(Error::MultipleErrors(errors));
        }
    }

    let mut result = Vec::new();

    match graph.topological_sort() {
        Ok(sorted) => {
            // FIXME: covered is just a sanity-check, should be removeable
            debug!("using order {:?}", sorted);
            let mut seen_undeclared : HashSet<&'a str> = HashSet::new();
            let mut covered = known_values.clone();
            let mut errors = Vec::new();
            for name in sorted {
                debug!("processing {:?}", name);
                match assignments.get(name) {
                    Some(expr) => {
                        for in_name in expr.referenced_wires() {
                            seen_undeclared.remove(&in_name);
                            assert!(covered.contains(&in_name));
                        }
                        if let Some(the_width) = widths.get(name) {
                            match expr.get_width_and_check(widths, constants) {
                                Ok(width) => {
                                    if let Err(e) = the_width.combine_expr_and_wire(width, name, expr) {
                                        errors.push(e);
                                    }
                                    result.push(Action::Assign(
                                        String::from(name),
                                        (*expr).clone(),
                                        *the_width,
                                    ));
                                }
                                Err(e) => {
                                    errors.push(e);
                                }
                            }
                        } else {
                            errors.push(Error::UndeclaredWireAssigned {
                                name: String::from(name),
                                span: *assign_spans.get(name).unwrap(),
                                close_name: find_close_names_in(name, widths.keys().into_iter().cloned()).or_else(|| {
                                    find_close_names_in(name, constants.keys().into_iter().map(|x| x.as_str()))
                                })
                            });
                        }
                    },
                    None => {
                        match fixed_by_output.get(name) {
                            Some(fixed) => {
                                for in_name in &fixed.in_wires {
                                    assert!(covered.contains(in_name.name.as_str()));
                                }
                                result.push(fixed.action.clone());
                            },
                            None => {
                                match wire_decl_spans.get(name) {
                                    Some(span) => {
                                        errors.push(Error::UnsetWire(String::from(name), *span));
                                    },
                                    None => {
                                        seen_undeclared.insert(name);
                                    },
                                }
                            }
                        }
                    }
                }
                covered.insert(name);
            }
            for name in seen_undeclared {
                // FIXME: this is probably really an internal error
                //        since any undeclared wire should either be fixed
                //        functionality or have a use
                // Assuming this is true, we should just be able to assert!() here
                errors.push(Error::UnsetUndeclaredWire(String::from(name)));
            }
            if errors.len() > 0 {
                return Err(Error::MultipleErrors(errors))
            }
        },
        Err(cycle) => {
            return Err(Error::WireLoop(cycle.into_iter().map(String::from).collect()));
        }
    }

    for fixed in &fixed_no_output {
        result.push(fixed.action.clone());
    }

    return Ok(result);
}

pub const Y86_PREAMBLE: &'static str = "
const STAT_BUB = 0b000, STAT_AOK = 0b001, STAT_HLT = 0b010;  # expected behavior
const STAT_ADR = 0b011, STAT_INS = 0b100, STAT_PIP = 0b110;  # error conditions

const REG_RAX = 0b0000, REG_RCX = 0b0001, REG_RDX = 0b0010, REG_RBX = 0b0011;
const REG_RSP = 0b0100, REG_RBP = 0b0101, REG_RSI = 0b0110, REG_RDI = 0b0111;
const REG_R8  = 0b1000, REG_R9  = 0b1001, REG_R10 = 0b1010, REG_R11 = 0b1011;
const REG_R12 = 0b1100, REG_R13 = 0b1101, REG_R14 = 0b1110, REG_NONE= 0b1111;

# icodes; see figure 4.2
const HALT   = 0b0000, NOP    = 0b0001, RRMOVQ = 0b0010, IRMOVQ = 0b0011;
const RMMOVQ = 0b0100, MRMOVQ = 0b0101, OPQ    = 0b0110, JXX    = 0b0111;
const CALL   = 0b1000, RET    = 0b1001, PUSHQ  = 0b1010, POPQ   = 0b1011;
const CMOVXX = RRMOVQ;

# ifuns; see figure 4.3
const ALWAYS = 0b0000, LE   = 0b0001, LT   = 0b0010, EQ   = 0b0011;
const NE     = 0b0100, GE   = 0b0101, GT   = 0b0110;
const ADDQ   = 0b0000, SUBQ = 0b0001, ANDQ = 0b0010, XORQ = 0b0011;

const true = 1;
const false = 0;
const TRUE = 1;
const FALSE = 0;
";

fn check_double_declare<'a, 'b>(errors: &'b mut Vec<Error>, name: &'a str, span: Span,
                       wire_decl_spans: &'b mut HashMap<&'a str, Span>,
                       wires: &'b HashMap<&'a str, WireWidth>) {
    match wire_decl_spans.get(name) {
        Some(other_span) => {
            errors.push(
                Error::RedeclaredWire(String::from(name), span, *other_span)
            );
        },
        None => {
            if wires.contains_key(name) {
                errors.push(
                    Error::RedeclaredBuiltinWire(String::from(name), span)
                );
            }
        },
    }
    wire_decl_spans.insert(name, span);
}

#[derive(Debug,Clone)]
pub struct LabelHolder {
    labels: Vec<WiretagMarker>  

}
#[derive(Debug,Clone)]
pub struct WiretagMarker {
    low: u8,
    high: u8,
    from: String, 
    to: String,  

}

impl WiretagMarker {
    pub fn new(l: u8,h: u8,f: String, t:String) -> WiretagMarker{
        WiretagMarker{low:l,high:h,from:f, to:t}
    }

    pub fn get_from(&self) -> String {
        return self.from.clone()
    }
    pub fn get_to(&self) -> String {
        return self.to.clone()
    }
    pub fn get_low(&self) -> u8 {
        return self.low.clone()
    }
    pub fn get_high(&self) -> u8 {
        return self.high.clone()
    }
}
#[derive(Debug,Clone)]
pub struct FakeMux {
    pub out: String,
    pub values: Vec<String>,
}
impl FakeMux {
    pub fn new(s: String) -> FakeMux{
       FakeMux{out:s,values:Vec::new()}
        
    }
    pub fn add_value(&mut self,ex: String)
    {
        self.values.push(ex.clone());
    }
}
#[derive(Debug,Clone)]
pub struct Wireassign {
    pub left: String,
    pub right: Vec<String>,
}
impl Wireassign {
    pub fn new(s: String) -> Wireassign{
       Wireassign{left:s,right:Vec::new()}
        
    }
    pub fn add_string(&mut self,ex: String)
    {
        self.right.push(ex.clone());
    }
}
impl Program {
pub fn bin_op_to_string(&self,boc:BinOpCode) -> String
{
    match boc {
                                        
        BinOpCode::Add => return String::from("+"),
        BinOpCode::Sub => return String::from("-"),
        BinOpCode::Mul => return String::from("*"),
        BinOpCode::Div => return String::from("/"),  
        BinOpCode::Or =>  return String::from("|"),
        BinOpCode::Xor => return String::from("^"),
        BinOpCode::And => return String::from("&"),
        BinOpCode::Equal => return String::from("="),
        BinOpCode::NotEqual => return String::from("!="),
        BinOpCode::LessEqual => return String::from("<="),
        BinOpCode::GreaterEqual => return String::from(">="),
        BinOpCode::Less => return String::from("<"),
        BinOpCode::Greater => return String::from(">"),
        BinOpCode::LogicalAnd => return String::from("&&"),  
        BinOpCode::LogicalOr =>  return String::from("||"),
        BinOpCode::LeftShift =>  return String::from(">>"),
        BinOpCode::RightShift => return String::from("<<"),
        BinOpCode::Error => panic!("unreported parse error"),

    }                                

}
pub fn un_op_to_string(&self,uoc:UnOpCode) -> String
{
    match uoc {
                                        
        UnOpCode::Plus => return String::from("+"),
        UnOpCode::Negate => return String::from("-"),
        UnOpCode::Complement => return String::from("~"),
        UnOpCode::Not => return String::from("!"),

    }                                

}

pub fn get_all_mux(&self)-> Vec<FakeMux>
{

    let mut vfm=Vec::new();
    for action in &self.actions
    {

         match action{
            Action::Assign(ref name, ref se, _) =>{
                
                
                match se.to_expr() {
                    Expr::Mux(ref v)=>{
                        let mut fm = FakeMux::new(name.to_string());
                        for opt in v{
                            match opt.value.to_expr() {
                                Expr::BinOp(ref boc, ref left, ref right)=>{
                                    let mut boc_string= self.bin_op_to_string(*boc);
                                    let mut lft:String=String::new();
                                    let mut rgt:String= String::new();
                                    match left.to_expr()
                                    {
                                        Expr::Constant(ref wv)=>{lft=format!("{}", wv.bits);},
                                        Expr::NamedWire(ref name)=>{lft=format!("{}", *name);},
                                        Expr::UnOp(ref uoc, ref covered) =>{
                                            let mut uoc_string= self.un_op_to_string(*uoc);
                                            let mut uoc_exp:String= String::new();
                                            match covered.to_expr() {
                                                Expr::Constant(ref wv)=>{uoc_exp=format!("{}", wv.bits);},
                                                Expr::NamedWire(ref name)=>{uoc_exp=format!("{}", *name);},

                                                _=>{}
                                            }
                                            lft.push_str(&uoc_string);
                                            lft.push_str(uoc_exp.as_str());
                                           
                                        }
                                        _=>{}
                                    }
                                    match right.to_expr() {
                                        Expr::Constant(ref wv)=>{rgt=format!("{}", wv.bits);},
                                        Expr::NamedWire(ref name)=>{rgt=format!("{}", *name);},
                                        Expr::UnOp(ref uoc, ref covered) =>{
                                            let mut uoc_string= self.un_op_to_string(*uoc);
                                            let mut uoc_exp:String= String::new();
                                            match covered.to_expr() {
                                                Expr::Constant(ref wv)=>{uoc_exp=format!("{}", wv.bits);},
                                                Expr::NamedWire(ref name)=>{uoc_exp=format!("{}", *name);},

                                                _=>{}
                                            }
                                            rgt.push_str(&uoc_string);
                                            rgt.push_str(uoc_exp.as_str());
                                            
                                        }
                                        _=>{}
                                    }
                                    let mut temp_str=String::from(lft);
                                    temp_str.push_str(&boc_string);
                                    temp_str.push_str(&rgt);
                                    fm.add_value(temp_str.clone());
                            },
                                Expr::Constant(ref wv)=>{fm.add_value(format!("{}", wv.bits));},
                                Expr::NamedWire(ref name)=>{fm.add_value(format!("{}", *name));},
                                Expr::UnOp(ref uoc, ref covered) =>{
                                    let mut uoc_string= self.un_op_to_string(*uoc);
                                    let mut uoc_exp=String::new();

                                    match covered.to_expr() {
                                        Expr::Constant(ref wv)=>{uoc_exp=format!("{}", wv.bits);},
                                        Expr::NamedWire(ref name)=>{uoc_exp=format!("{}", *name);},

                                        _=>{}
                                    }
                                    let mut temp_str=String::new();
                                    temp_str.push_str(uoc_string.as_str());
                                    temp_str.push_str(uoc_exp.as_str());
                                    fm.add_value(temp_str)


                                }
                                _=>{}

                            }


                        }
                        vfm.push(fm);
                    },
                    _=>{}
                }
                 
            },
            _=>{}
        }

       
    }
    vfm

}


pub fn get_all_wire_assignments(&self)->Vec<Wireassign>
{
    let mut vwa:Vec<Wireassign>=Vec::new();
    for action in &self.actions
    {
        match action{
            Action::Assign(ref name, ref se, _) =>{
                let mut w_a:Wireassign = Wireassign::new(name.to_string());
                match se.to_expr() {
                    Expr::BinOp(ref boc, ref left, ref right)=>{
                        let mut middle= self.bin_op_to_string(*boc);
                        let mut lft:String=String::new();
                        let mut rgt:String= String::new();
                        match left.to_expr() {
                            Expr::Constant(ref wv)=>{lft=format!("{}", wv.bits);},
                            Expr::NamedWire(ref name)=>{lft=format!("{}", *name);},
                            _=>{}
                        }
                        match right.to_expr() {
                            Expr::Constant(ref wv)=>{rgt=format!("{}", wv.bits);},
                            Expr::NamedWire(ref name)=>{rgt=format!("{}", *name);},
                            _=>{}
                        }
                        w_a.add_string(lft);
                        w_a.add_string(middle);
                        w_a.add_string(rgt);
                        vwa.push(w_a);
                    },
                    Expr::Constant(ref wv)=>{

                        w_a.add_string(format!("{}", wv.bits));
                        vwa.push(w_a);
                    },
                    Expr::NamedWire(ref name)=>{
                        w_a.add_string(format!("{}", *name));
                        vwa.push(w_a);
                    },
                    Expr::UnOp(ref code , ref se) =>{
                        w_a.add_string(format!("{}", self.un_op_to_string(*code)));
                        let mut lft:String=String::new();
                        match se.to_expr() {


                            Expr::Constant(ref wv)=>{lft=format!("{}", wv.bits);},
                            Expr::NamedWire(ref name)=>{lft=format!("{}", *name);},
                            _=>{}
                        }
                        w_a.add_string(lft);
                        vwa.push(w_a);


                    },
                    _=>{}
                }
            },
            _=>{}
        }
    }
    vwa
}
pub fn get_all_reg(&self)-> Vec<RegisterBank>{

    return self.register_banks.clone();
}
pub fn print_all_registers(&self){
    for register in self.register_banks.clone(){
        self.print_register(register);
    }
fn print_register(&self,reg: RegisterBank)
{

    println!("{}",reg.label );
    for sig in reg.signals
    {

        println!(" the in signal is {} and the out signal is {}",sig.0,sig.1 );

    }

}
pub fn label_wires(&self) -> Vec<WiretagMarker>
     {
        let mut hm= HashMap::new();
        let mut es:Vec<WiretagMarker> = Vec::new();
        let mut change=true;
        let mut count: u32;
        let mut done:bool;
       
        while change 
        {
           change=false;
           count=0;   
            'action_loop :for action in &self.actions
            {
                match hm.get(&count) {
               Some(&_int) => {
                done=true;
            },
               _ => {
                done=false;
            }
           }
                if !done {
                let mut temp_vec=es.clone();
                match action{
                    Action::Assign(ref name, ref se, _) =>{
                        match se.to_expr() {
                            Expr::BitSelect{ref from, low, high} =>{
                                match from.to_expr() {
                                    Expr::NamedWire (ref str_name) => {
                                        if str_name=="i10bytes" {
                                           es.push(WiretagMarker::new(*low,*high,str_name.to_string(),name.to_string()));
                                            change=true;
                                            hm.insert(count,"valid");
                                        }
                                        else {
                                            'temp_vec_loop :for wiretag_marker in temp_vec{
                                                if wiretag_marker.to== str_name.to_string(){
                                                    es.push(WiretagMarker::new(*low,*high, wiretag_marker.from, name.to_string()));
                                                    change=true;
                                                    hm.insert(count,"valid");
                                                    //break 'temp_vec_loop;
                                                }
                                            }

                                        }
                                    },
                                    _=>{}
                                }
                            },
                            _=>{}  
                        }
                    },
                    _=>{}

                 }
                 count=count+1;
             }
            }
        }
        es
}


pub fn get_pc(&self) -> String {
    let mut s = String::new();
    for action in &self.actions{
        match action{
            Action::Assign(ref name, ref se, _) =>{
                if name=="pc"{
                   match se.to_expr(){
                        Expr::NamedWire(ref wire) =>{
                            s.push_str(wire)
                        },
                        _ =>{   
                        }
                   }
                }
            },
            _ =>{
                
            },
        }
    }
    s
}

fn find_reg(&self, name:String)-> String{

    let mut flag:bool = false;
    let mut s:String= String::new();
    for bank in &self.register_banks{
        if flag==false{
        for sig in &bank.signals{
            if sig.0==name&& flag==false{
                s.push_str(&bank.label);
                flag=true;
            }
            if sig.1==name && flag==false{
               s.push_str(&bank.label);
                flag=true;
            }

        }
    }
    }
    s
}
pub fn get_pc_reg(&self)-> String{
return self.find_reg(self.get_pc());

}
    pub fn new_y86(statements: Vec<Statement>) -> Result<Program, Error> {
        Program::new(statements, y86_fixed_functions())
    }

    pub fn new(
        statements: Vec<Statement>,
        fixed_functions: Vec<FixedFunction>
    ) -> Result<Program, Error> {
        // Step 1: Split statements into constant declarations, wire declarations, assignments
        let mut constants_raw: HashMap<&str, &SpannedExpr> = HashMap::new();
        let mut wires = HashMap::new();
        let mut wire_decl_spans = HashMap::new();
        let mut assign_spans = HashMap::new();
        let mut needed_wires = HashSet::new();
        let mut assignments = HashMap::new();
        let mut register_banks_raw = Vec::new();
        let mut fixed_out_wires = HashSet::new();
        let mut register_in_spans = HashMap::new();
        let mut errors = Vec::new();
        for fixed in &fixed_functions {
            for ref in_wire in &fixed.in_wires {
                wires.insert(in_wire.name.as_str(), in_wire.width);
            }
            for ref decl in &fixed.out_wire {
                wires.insert(decl.name.as_str(), decl.width);
                fixed_out_wires.insert(decl.name.as_str());
            }
        }
        for statement in &statements {
            match *statement {
                Statement::ConstDecls(ref decls) => {
                    for ref decl in decls {
                        check_double_declare(&mut errors, decl.name.as_str(), decl.name_span,
                                        &mut wire_decl_spans, &wires);
                        constants_raw.insert(decl.name.as_str(), &decl.value);
                    }
                },
                Statement::WireDecls(ref decls) => {
                    for ref decl in decls {
                        check_double_declare(&mut errors, decl.name.as_str(), decl.span,
                                        &mut wire_decl_spans, &wires);
                        wires.insert(decl.name.as_str(), decl.width);
                        needed_wires.insert(decl.name.as_str());
                    }
                },
                Statement::Assignments(ref assigns) => {
                    for assign in assigns {
                        for &(ref name, ref span) in &assign.names {
                            if assign_spans.contains_key(name.as_str()) {
                                errors.push(
                                    Error::DoubleAssignedWire(
                                        name.clone(), *span,
                                        *assign_spans.get(name.as_str()).unwrap(),
                                    )
                                );
                            } else if fixed_out_wires.contains(name.as_str()) {
                                errors.push(
                                    Error::DoubleAssignedFixedOutWire(
                                        name.clone(), *span,
                                    )
                                );
                            }
                            assignments.insert(name.as_str(), &assign.value);
                            assign_spans.insert(name.as_str(), span.clone());
                        }
                    }
                },
                Statement::RegisterBankDecl(ref decl) => {
                    register_banks_raw.push(decl);
                },
                Statement::Error => {
                    /* panic since we should report this and give up earlier */
                    panic!("statement did not parse correctly");
                },
            }
        }

        debug!("const decls: {:?}", constants_raw);
        debug!("wire decls: {:?}", wires);
        debug!("assignments: {:?}", assignments);

        for (_, expr) in &constants_raw {
            for in_name in expr.referenced_wires() {
                let is_constant = constants_raw.contains_key(&in_name);
                if wires.contains_key(&in_name) && !is_constant {
                    for usage in expr.find_references(in_name).into_iter() {
                        errors.push(Error::NonConstantWireRead(String::from(in_name), usage));
                    }
                } else if !is_constant {
                    for usage in expr.find_references(in_name).into_iter() {
                        errors.push(Error::UndeclaredWireRead {
                            name: String::from(in_name),
                            expr: usage,
                            close_name: find_close_names_in(in_name, constants_raw.keys().into_iter().cloned()),
                        });
                    }
                }
            }
        }

        if errors.len() > 0 {
            return Err(Error::MultipleErrors(errors));
        }

        // Step 2: find constants values
        let constants = resolve_constants(&constants_raw)?;

        // Step 3: resolve register banks
        let mut defaulted_wires : HashSet<String> = HashSet::new();
        let mut register_banks = Vec::new();
        let mut errors = Vec::new();
        let mut seen_registers : HashMap<String, Span> = HashMap::new();
        for decl in &register_banks_raw {
            // FIXME: should really iterate over graphemes
            let name_chars: Vec<char> = decl.name.chars().collect();
            if name_chars.len() != 2 {
                errors.push(Error::InvalidRegisterBankName(decl.name.clone(), decl.name_span));
                continue;
            }
            let in_prefix = name_chars[0];
            let out_prefix = name_chars[1];
            if !in_prefix.is_lowercase() || !out_prefix.is_uppercase() {
                errors.push(Error::InvalidRegisterBankName(decl.name.clone(), decl.name_span));
                continue;
            }
            let mut signals = Vec::new();
            let mut defaults = HashMap::new();
            let mut stall_signal = String::from("stall_");
            stall_signal.push(out_prefix);
            let mut bubble_signal = String::from("bubble_");
            bubble_signal.push(out_prefix);
            if !assignments.contains_key(stall_signal.as_str()) {
                debug!("{:?} is not assigned", stall_signal);
                defaulted_wires.insert(stall_signal.clone());
            }
            if !assignments.contains_key(bubble_signal.as_str()) {
                debug!("{:?} is not assigned", bubble_signal);
                defaulted_wires.insert(bubble_signal.clone());
            }
            for register in &decl.registers {
                let mut in_name = String::new();
                let mut out_name = String::new();
                in_name.push(in_prefix);
                out_name.push(out_prefix);
                in_name.push('_');
                out_name.push('_');
                in_name.push_str(register.name.as_str());
                out_name.push_str(register.name.as_str());
                let mut found_error = false;
                // FIXME: redundant with code in resolve_constants()
                for referenced in register.default.referenced_wires() {
                    if wires.contains_key(referenced) && !constants.contains_key(referenced) {
                        found_error = true;
                        for expr in register.default.find_references(referenced).into_iter() {
                            errors.push(Error::NonConstantWireRead(String::from(referenced), expr));
                        }
                    }
                }
                if defaults.contains_key(&out_name) {
                    found_error = true;
                    errors.push(Error::DuplicateRegister {
                        bank: decl.name.clone(),
                        register_name: register.name.clone(),
                    });
                }
                if assignments.contains_key(out_name.as_str()) {
                    found_error = true;
                    errors.push(Error::DoubleAssignedRegisterWire {
                        name: out_name.clone(),
                        assign_span: assign_spans.get(out_name.as_str()).unwrap().clone(),
                        register_span: register.span.clone(),
                    });
                }
                if seen_registers.contains_key(&out_name) {
                    found_error = true;
                    errors.push(Error::DoubleDeclaredRegisterOutWire {
                        name: String::from(out_name.clone()),
                        old_span: seen_registers.get(&out_name).unwrap().clone(),
                        new_span: register.span.clone(),
                    })
                } else {
                    seen_registers.insert(out_name.clone(), register.span.clone());
                }

                if found_error {
                    continue;
                }

                match register.default.evaluate(&constants) {
                    Ok(value) => {
                        if None == value.width.combine(register.width) {
                            errors.push(Error::MismatchedRegisterDefaultWidths {
                                bank: decl.name.clone(),
                                register_name: register.name.clone(),
                                register_width: register.width,
                                default_expression: register.default.clone(),
                                expression_width: value.width,
                            });
                        }
                        defaults.insert(out_name.clone(), value.as_width(register.width));
                        register_in_spans.insert(in_name.clone(), register.span.clone());
                        debug!("Generated wires {} and {} for register", in_name, out_name);
                        signals.push((in_name, out_name, register.width));
                    },
                    Err(e) => { errors.push(e); }
                }
            }
            register_banks.push(RegisterBank {
                label: decl.name.clone(),
                signals: signals,
                defaults: defaults,
                stall_signal: stall_signal,
                bubble_signal: bubble_signal,
            });
        }

        let actions = {
            // create nonmutable reference so we can borrow strings from register banks
            let register_banks = &register_banks;
            // move wires and needed_wires so they are dropped before register_banks
            let mut wires = wires;
            let mut needed_wires = needed_wires;

            // track widths, values we do/don't need assignment statements for
            let mut known_values = HashSet::new();
            for bank in register_banks {
                for signal in &bank.signals {
                    let in_name = &signal.0;
                    let out_name = &signal.1;
                    let width = signal.2;
                    wires.insert(out_name.as_str(), width);
                    known_values.insert(out_name.as_str());
                    wires.insert(in_name.as_str(), width);
                    needed_wires.insert(in_name.as_str());
                }
                wires.insert(bank.stall_signal.as_str(), WireWidth::Bits(1));
                wires.insert(bank.bubble_signal.as_str(), WireWidth::Bits(1));
            }

            // Step 4: Check for missing wires
            for name in needed_wires {
                if !assignments.contains_key(name) {
                    if let Some(span) = wire_decl_spans.get(name) {
                            errors.push(Error::UnsetWire(String::from(name), *span));
                    } else if let Some(span) = register_in_spans.get(name) {
                        errors.push(Error::UnsetRegisterInputWire {
                            name: String::from(name),
                            register_span: *span,
                        });
                    } else {
                        errors.push(Error::UnsetBuiltinWire(String::from(name)));
                    }
                }
            }

            // Step 5: order remaining assignments
            for key in constants_raw.keys() {
                known_values.insert(*key);
                wires.insert(key, constants.get(&String::from(*key)).unwrap().width);
            }

            if errors.len() > 0 {
                return Err(Error::MultipleErrors(errors));
            }

            // FIXME: do we actually need to pass wire_decl_spans, or
            //        can we be assured all errors that need that will be caught above?
            assignments_to_actions(&assignments, &wires,
                                   &known_values, &fixed_functions,
                                   &wire_decl_spans, &assign_spans,
                                   &constants)?
        };

        Ok(Program {
            constants: constants,
            actions: actions,
            register_banks: register_banks,
            defaulted_wires: defaulted_wires,
        })
    }

    pub fn constants(&self) -> WireValues {
        self.constants.clone()
    }

    pub fn initial_state(&self) -> WireValues {
        let mut values = self.constants();
        for bank in &self.register_banks {
            for signal in &bank.signals {
                let in_name = &signal.0;
                let out_name = &signal.1;
                let the_value = *bank.defaults.get(out_name).unwrap();
                values.insert(in_name.clone(), the_value);
                values.insert(out_name.clone(), the_value);
            }
            values.insert(bank.bubble_signal.clone(), WireValue::false_value());
            values.insert(bank.stall_signal.clone(), WireValue::false_value());
        }
        values
    }

    fn process_register_banks(&self, values: &mut WireValues) -> Result<(), Error> {
        for bank in &self.register_banks {
            let stalled = values.get(&bank.stall_signal).unwrap().is_true();
            let bubbled = values.get(&bank.bubble_signal).unwrap().is_true();
            // FIXME: correct stall + bubble behavior
            if bubbled {
                debug!("bubble {}", bank.bubble_signal);
                for (k, v) in &bank.defaults {
                    *values.get_mut(k).unwrap() = *v;
                }
            } else if !stalled {
                for signal in &bank.signals {
                    let in_name = &signal.0;
                    let out_name = &signal.1;
                    debug!("copy {} -> {}", in_name, out_name);
                    let new_value = *values.get(in_name).unwrap();
                    *values.get_mut(out_name).unwrap() = new_value;
                }
            }
        }
        Ok(())
    }

    pub fn defaulted_wires(&self) -> &HashSet<String> {
        return &self.defaulted_wires;
    }
}

#[derive(Debug)]
pub struct Memory {
    data: BTreeMap<u64, u8>
}

impl Memory {
    pub fn new() -> Memory {
        Memory { data: BTreeMap::new() }
    }

    fn load_line_y86(&mut self, expect_loc: u64, line: &str) -> Result<u64, ()> {
        debug!("processing line from yo file {}", line);
        if &line[0..2] == "0x" && &line[5..7] == ": " && &line[27..29] == " |" {
            if let Ok(loc) = u64::from_str_radix(&line[2..5], 16) {
                if loc != expect_loc {
                    debug!("loc {} from natural loc {}", loc, expect_loc);
                }
                let mut loc = loc;
                let hex_chars = &line[7..27];
                let mut i = 0;
                while i < hex_chars.len() && &hex_chars[i..(i+1)] != " " {
                    if let Ok(byte) = u8::from_str_radix(&hex_chars[i..(i+2)], 16) {
                        self.data.insert(loc, byte);
                        debug!("loaded {:x} -> {:x}", byte, loc);
                        loc += 1;
                        i += 2;
                    } else {
                        debug!("non-hexadecimal data {}", &hex_chars[i..(i+2)]);
                        return Err(());
                    }
                }
                return Ok(loc);
            } else {
                debug!("bad address 0x{}", &line[2..5]);
                return Err(());
            }
        } else if line.contains("|") && !line.starts_with("                            |") {
            // assume this is meant to contain data
            debug!("found pipe, but not other parts of yas format");
            return Err(());
        } else {
            debug!("ignoring line {}", line);
            return Ok(expect_loc);
        }
    }

    pub fn load_from_y86<R: BufRead>(&mut self, reader: &mut R) -> Result<(), Error> {
        /* 0x000: 30f40001000000000000 |     irmovq $256, %rsp */
        /* 01234567890123456789012345678 */
        /*           1111111111222222222 */
        let mut found_something = false;
        let mut next_loc: u64 = 0x0;
        for maybe_line in reader.lines() {
            let line = maybe_line?;
            if let Ok(new_loc) = self.load_line_y86(next_loc, &line) {
                found_something = true;
                next_loc = new_loc;
            } else {
                return Err(Error::UnparseableLine(String::from(line)));
            }
        }
        if !found_something {
            return Err(Error::EmptyFile());
        }
        debug!("after loading from yo file: {} items", self.data.len());
        Ok(())
    }

    pub fn read(&self, address: u64, bytes: u8) -> WireValue {
        assert!(bytes <= 16);
        let mut result = 0;
        let mut remaining = bytes;
        let total = remaining;
        let mut cur_addr = address;
        debug!("reading {:#x} ({:?} bytes)", address, bytes);
        while remaining > 0 {
            result |= (*self.data.get(&cur_addr).unwrap_or(&0) as u128) << ((total - remaining) * 8);
            debug!("reading {:#x}; accumulated result is {:#x}", cur_addr, result);
            cur_addr = cur_addr.wrapping_add(1);
            remaining -= 1;
        }
        WireValue { bits: result, width: WireWidth::Bits(bytes * 8) }
    }

    pub fn write(&mut self, address: u64, value: u128, bytes: u8) {
        assert!(bytes <= 16);
        let mut remaining = bytes;
        let total = remaining;
        let mut cur_addr = address;
        debug!("write {:#x} ({:?} bytes) into {:#x}", value, bytes, address);
        while remaining > 0 {
            let to_write = (value >> ((total - remaining) * 8)) as u8;
            debug!("writing {:#x} into {:#x}", to_write, cur_addr);
            self.data.insert(cur_addr, to_write);
            cur_addr = cur_addr.wrapping_add(1);
            remaining -= 1;
        }
    }

    fn dump_memory_y86<W: Write>(&self, result: &mut W) -> Result<(), Error> {
        writeln!(result,   "| used memory:   _0 _1 _2 _3  _4 _5 _6 _7   _8 _9 _a _b  _c _d _e _f    |")?;
        if self.data.len() == 0 {
            return Ok(());
        }
        let mut cur_addr: u64 = *self.data.iter().next().unwrap().0;
        for (&k, &v) in &self.data {
            debug!("found memory {:x}={:x}", k, v);
            while cur_addr <= k {
                debug!("output addr {:x}", cur_addr);
                if cur_addr % 16 == 0 {
                    cur_addr = (k >> 4) << 4;
                    write!(result, "|  0x{:07x}_:  ", cur_addr >> 4)?;
                }
                if cur_addr == k {
                    write!(result, " {:02x}", v)?;
                } else {
                    write!(result, "   ")?;
                }
                match cur_addr % 16 {
                    3 | 11 => {write!(result, " ")?;},
                    7 => {write!(result, "  ")?;},
                    _ => {},
                }
                if cur_addr % 16 == 15 {
                    write!(result, "    |\n")?;
                }
                cur_addr = cur_addr.wrapping_add(1);
                if cur_addr == 0 {
                    break
                }
            }
        }
        while cur_addr % 16 != 0 {
            match cur_addr % 16 {
                15 => write!(result, "       |\n")?,
                3 | 11 => write!(result, "    ")?,
                7 => write!(result, "     ")?,
                _ => write!(result, "   ")?,
            };
            cur_addr = cur_addr.wrapping_add(1);
        }
        Ok(())
    }
}

pub struct RunOptions {
    trace_assignments: bool,
    trace_fixed_functionality: bool,
    show_wire_values: bool,
    show_register_banks_with_registers: bool,
    show_registers_and_memory: bool,
    show_disassembly: bool,
    timeout: u32,
    prompt: Option<Box<dyn Fn() -> ()>>
}

impl Debug for RunOptions {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "RunOptions {{ trace_assignments: {:?}, trace_fixed_functionality: {:?}, show_wire_values: {:?}, show_register_banks_with_registers: {:?}, show_registers_and_memory: {:?}, show_disassembly: {:?}, timeout: {:?}, .. }}",
            self.trace_assignments,
            self.trace_fixed_functionality,
            self.show_wire_values,
            self.show_register_banks_with_registers,
            self.show_registers_and_memory,
            self.show_disassembly,
            self.timeout
        )
    }
}

impl Default for RunOptions {
    fn default() -> RunOptions {
        RunOptions {
            trace_assignments: false,
            trace_fixed_functionality: false,
            show_wire_values: false,
            show_register_banks_with_registers: true,
            show_registers_and_memory: true,
            show_disassembly: true,
            timeout: 9999,
            prompt: None,
        }
    }
}

impl RunOptions {
    pub fn set_quiet(&mut self) {
        self.show_wire_values = false;
        self.show_registers_and_memory = false;
        self.show_disassembly = false;
    }

    pub fn set_test(&mut self) {
        self.show_register_banks_with_registers = false;
    }

    pub fn set_debug(&mut self) {
        self.trace_fixed_functionality = true;
        self.show_wire_values = true;
    }

    pub fn set_trace(&mut self) {
        self.trace_fixed_functionality = true;
        self.trace_assignments = true;
    }

    pub fn set_timeout(&mut self, new_timeout: u32) {
        self.timeout = new_timeout;
    }

    pub fn set_prompt(&mut self, new_prompt: Box<dyn Fn() -> ()>) {
        self.prompt = Some(new_prompt);
    }
}

#[derive(Debug)]
pub struct RunningProgram {
    program: Program,
    cycle: u32,
    values: WireValues,
    memory: Memory,
    registers: Vec<u64>,
    zero_register: usize,
    last_status: Option<u8>,
    options: RunOptions,
}


const Y86_STATUSES: [&'static str; 6] = [
    "0 (Bubble)",
    "1 (OK)",
    "2 (Halt)",
    "3 (Invalid Address)",
    "4 (Invalid Instruction)",
    "5 (Pipeline Error)"
];

impl RunningProgram {
    pub fn new(program: Program,
               num_registers: usize,
               zero_register: usize) -> RunningProgram {
        let values = program.initial_state();
        let mut registers = Vec::new();
        for _ in 0..num_registers {
            registers.push(0);
        }
        RunningProgram {
            program: program,
            cycle: 0,
            values: values,
            memory: Memory::new(),
            registers: registers,
            zero_register: zero_register,
            last_status: None,
            options: RunOptions::default(),
        }
    }
    pub fn get_all_muxes(&self)->Vec<FakeMux>{

        return self.program.get_all_mux();
    }
    pub fn print_all_muxes(&self){
        let temp=self.get_all_muxes();
        for fm in temp{
            println!("output of the mux goes to {}", fm.out);
            println!("the possible values are");
            for val in fm.values{
                print!(" {} ", val );
            }
            println!("");

        }

    }
    fn get_all_wire_assignments(&self)->Vec<Wireassign>{

        return self.program.get_all_wire_assignments();
    }
    pub fn print_all_wire_assignments(&self)
    {
        let temp=self.get_all_wire_assignments();
        for w_a in temp{
            let mut temp_str= String::new();
            if w_a.right.len()==1 {
                temp_str.push_str(w_a.left.as_str());
                temp_str.push_str("=");
                temp_str.push_str(w_a.right[0].as_str());
            }
            if w_a.right.len()==2 {
                temp_str.push_str(w_a.left.as_str());
                temp_str.push_str("=");
                temp_str.push_str(w_a.right[0].as_str());
                temp_str.push_str(w_a.right[1].as_str());

                
            }
            if w_a.right.len()==3 {
                temp_str.push_str(w_a.left.as_str());
                temp_str.push_str("=");
                temp_str.push_str(w_a.right[0].as_str());
                temp_str.push_str(w_a.right[1].as_str());
                temp_str.push_str(w_a.right[2].as_str());
                
            }

            println!("{}",temp_str );
        }

    fn get_full_pc(&self)-> (String,String){
        let pc = self.program.get_pc();
        let pc_reg=self.program.get_pc_reg();
        return (pc,pc_reg)
    }
    fn get_all_reg(&self)->Vec<RegisterBank>{
        return self.program.get_all_reg()
    }
    pub fn print_all_registers(&self)
    {

        self.program.print_all_registers();
    }
    pub fn parse_file_non_pipeline(&self) -> (String,String,Vec<WiretagMarker>, Vec<Wireassign>,Vec<FakeMux>, Vec<RegisterBank>) {
        let full_pc:(String,String)=self.get_full_pc();
        let parse_i10:Vec<WiretagMarker>=self.program.label_wires();
        let wire_assignments: Vec<Wireassign>=self.get_all_wire_assignments();
        let muxes:Vec<FakeMux>=self.get_all_muxes();
        let registers:Vec<RegisterBank>=self.get_all_reg();
        return(full_pc.0,full_pc.1,parse_i10, wire_assignments, muxes,registers)
    }
    pub fn set_options(&mut self, options: RunOptions) {
        self.options = options;
    }

    pub fn run<W: Write>(&mut self, out: &mut W) -> Result<(), Error> {
        while !self.done() {
            if self.options.show_registers_and_memory {
                self.dump_y86(out)?;
            }
            self.step_with_output(out)?;
            match self.options.prompt {
                Some(ref prompt) => prompt(),
                None => {}
            }
        }
        Ok(())
    }


    pub fn load_memory_y86<R: BufRead>(&mut self, reader: &mut R) -> Result<(), Error> {
        self.memory.load_from_y86(reader)
    }

    pub fn new_y86(program: Program) -> RunningProgram {
        RunningProgram::new(
            program,
            16,
            15
        )
    }

    // FIXME: assumes Y86
    fn name_register(&self, i: usize) -> &'static str {
        return name_register(i);
    }

    fn dump_values<W: Write>(&self, w: &mut W) -> Result<(), Error> {
        let mut keys: Vec<String> = self.values.keys().cloned().collect();
        keys.sort_unstable_by(|a, b| a.to_ascii_uppercase().cmp(&b.to_ascii_uppercase()).then(a.cmp(&b)));
        let mut max_name_len = 4;
        let mut max_value_len = 3;
        for key in &keys {
            if self.program.constants.contains_key(key) {
                continue
            }
            if self.program.defaulted_wires().contains(key) {
                continue
            }
            let value = self.values.get(key).unwrap();
            let value_width_bits = match value.width {
                WireWidth::Unlimited => 64,
                WireWidth::Bits(x) => x,
            };
            let value_width_len = (value_width_bits as usize + 3) / 4 + 2;
            max_name_len = max(key.len(), max_name_len);
            max_value_len = max(value_width_len, max_value_len);
        }
        debug!("max_value_len = {}; max_name_len = {};\n", max_value_len, max_name_len);
        writeln!(w, "Values of wires:")?;
        writeln!(w, "{:width$}  {:>value_width$}", "Wire", "Value", width=max_name_len, value_width=max_value_len)?;
        for key in &keys {
            if self.program.constants.contains_key(key) {
                continue
            }
            if self.program.defaulted_wires().contains(key) {
                continue
            }
            let value = self.values.get(key).unwrap();
            let value_width_bits = match value.width {
                WireWidth::Unlimited => 64,
                WireWidth::Bits(x) => x,
            };
            let value_width_len = (value_width_bits as usize + 3) / 4 + 2;
            let extra_len = max_value_len - value_width_len;
            writeln!(w, "{:width$}  {empty:extra_len$}{:#0value_width_len$x}", key,
                value.bits, width=max_name_len, value_width_len=value_width_len,
                extra_len=extra_len, empty="")?
        }

        Ok(())
    }

    pub fn step(&mut self) -> Result<(), Error> {
        self.step_with_output(&mut sink())
    }

    pub fn step_with_output<W: Write>(&mut self, out: &mut W) -> Result<(), Error> {
        for action in &self.program.actions {
            debug!("processing action {:?}", action);
            match action {
               &Action::Assign(ref name, ref expr, ref width) => {
                  let result = expr.evaluate(&self.values)?.as_width(*width);
                  if self.options.trace_assignments {
                      writeln!(out, "{} set to 0x{:x}", name, result.bits)?;
                  }
                  debug!("computed value {:?}", result);
                  let mut inserted = false;
                  if let Some(value) = self.values.get_mut(name) {
                      *value = result;
                      inserted = true;
                  }
                  if !inserted {
                      self.values.insert(name.clone(), result);
                  }
               },
               &Action::ReadMemory { ref is_read, ref address, ref out_port, ref bytes, ref is_instruction } => {
                   let do_read = match is_read {
                       &None => true,
                       &Some(ref wire) => self.values.get(wire).unwrap().is_true(),
                   };
                   if do_read {
                       let address_value = *self.values.get(address).unwrap();
                       let value = self.memory.read(address_value.bits as u64, *bytes);
                       if self.options.trace_fixed_functionality {
                           writeln!(out,
                                    "{} set to 0x{:x} (reading {} bytes from memory at {}=0x{:x})",
                                    out_port, value, bytes, address, address_value.bits)?;
                       }
                       self.values.insert(out_port.clone(), value);
                       if *is_instruction {
                           if self.options.show_disassembly {
                               write!(out, "pc = 0x{:x}; loaded [", address_value)?;
                               let (num_bytes, instruction) = disassemble_to_string(value.bits);
                               for i in 0..num_bytes {
                                   let cur_byte = ((value.bits >> (8 * i)) as u128) & 0xFF;
                                   write!(out, "{:02x} ", cur_byte)?;
                               }
                               writeln!(out, ": {}]", instruction)?;
                           }
                       }
                   } else {
                       if self.options.trace_fixed_functionality {
                           writeln!(out,
                                    "not reading from memory since {} is 0", is_read.clone().unwrap())?;
                       }
                       // keep the result well-defined
                       let zero = WireValue::new(0).as_width(WireWidth::from((bytes * 8) as usize));
                       self.values.insert(out_port.clone(), zero);
                   }
               },
               &Action::WriteMemory { ref is_write, ref address, ref in_port, ref bytes } => {
                   let do_write = match is_write {
                       &None => true,
                       &Some(ref wire) => self.values.get(wire).unwrap().is_true(),
                   };
                   if do_write {
                       let address_value = self.values.get(address).unwrap();
                       let input_value = self.values.get(in_port).unwrap();
                       if self.options.trace_fixed_functionality {
                           writeln!(out,
                                    "writing {}={} to memory at {}=0x{:x}",
                                    in_port, input_value, address, address_value)?;
                       }
                       self.memory.write(address_value.bits as u64, input_value.bits, *bytes);
                   } else if self.options.trace_fixed_functionality {
                       writeln!(out,
                                "not writing to memory since {} is 0", is_write.clone().unwrap())?;
                   }
               },
               &Action::SetStatus { ref in_wire } => {
                   self.last_status = Some(self.values.get(in_wire).unwrap().bits as u8);
               },
               &Action::ReadProgramRegister { ref number, ref out_port } => {
                   let number_wire = number;
                   let number = self.values.get(number_wire).unwrap().bits as usize;
                   if number < self.registers.len() {
                       self.values.insert(out_port.clone(),
                           WireValue { bits: self.registers[number].into(), width: WireWidth::Bits(64) }
                       );
                       if self.options.trace_fixed_functionality {
                           writeln!(out,
                                    "set {} to 0x{:x} from register {}={} ({})",
                                    out_port, self.registers[number],
                                    number_wire, number, self.name_register(number))?;
                       }
                   } else {
                       // should not be reached, but make sure behavior is consistent in case
                       self.values.insert(out_port.clone(), WireValue {
                           bits: 0, width: WireWidth::Bits(64)
                       });
                   }
               },
               &Action::WriteProgramRegister { ref number, ref in_port } => {
                   let number_wire = number;
                   let number = self.values.get(number_wire).unwrap().bits as usize;
                   if number < self.registers.len() && number != self.zero_register {
                       self.registers[number] = self.values.get(in_port).unwrap().bits as u64;
                       if self.options.trace_fixed_functionality {
                           writeln!(out,
                                    "writing {}=0x{:x} into register {}={} ({})",
                                    in_port, self.registers[number],
                                    number_wire, number, self.name_register(number))?;
                       }
                   }
               },
            }
        }
        // TODO: dump wire values here
        if self.options.show_wire_values {
            self.dump_values(out)?;
        }
        self.program.process_register_banks(&mut self.values)?;
        self.cycle += 1;

        Ok(())
    }

    pub fn cycle(&self) -> u32 { self.cycle }

    pub fn values(&self) -> &WireValues { &self.values }

    pub fn status_or_default(&self, default: u8) -> u8 {
        let value = self.values.get("Stat").unwrap_or(&WireValue::from_u64(default as u64)).bits;
        value as u8
    }

    // FIXME: hard-coded Y86 status codes
    pub fn done(&self) -> bool {
        (self.status_or_default(1) != 1 &&
         self.status_or_default(1) != 0
         ) || self.cycle >= self.options.timeout
    }

    pub fn halted(&self) -> bool {
        self.status_or_default(1) == 2
    }

    pub fn timed_out(&self) -> bool {
        self.cycle >= self.options.timeout
    }

    fn dump_program_registers_y86<W: Write>(&self, result: &mut W) -> Result<(), Error> {
        writeln!(result, "| RAX: {:16x}   RCX: {:16x}   RDX: {:16x} |",
            self.registers[0], self.registers[1], self.registers[2])?;
        writeln!(result, "| RBX: {:16x}   RSP: {:16x}   RBP: {:16x} |",
            self.registers[3], self.registers[4], self.registers[5])?;
        writeln!(result, "| RSI: {:16x}   RDI: {:16x}   R8:  {:16x} |",
            self.registers[6], self.registers[7], self.registers[8])?;
        writeln!(result, "| R9:  {:16x}   R10: {:16x}   R11: {:16x} |",
            self.registers[9], self.registers[10], self.registers[11])?;
        writeln!(result, "| R12: {:16x}   R13: {:16x}   R14: {:16x} |",
            self.registers[12], self.registers[13], self.registers[14])?;
        Ok(())
    }

    fn dump_bank<W: Write>(&self, result: &mut W, bank: &RegisterBank) -> Result<(), Error> {
        let mut line_loc = 0;
        let max_loc = 71;
        let bank_stalled = self.values.get(&bank.stall_signal).unwrap().is_true();
        let bank_bubbled = self.values.get(&bank.bubble_signal).unwrap().is_true();
        let status = if bank_bubbled { 'B' } else if bank_stalled { 'S' } else { 'N' };
        write!(result, "| register {}({}) {{", bank.label, status)?;
        line_loc += 18;
        for signal in &bank.signals {
            let name = signal.0.split_at(2).1;
            let width = signal.2;
            let hex_width = ((width.bits_or_128() + 3) / 4) as usize;
            if line_loc + 2 + hex_width + name.len() >= max_loc {
                while line_loc < max_loc {
                    write!(result, " ")?;
                    line_loc += 1;
                }
                write!(result, " |\n| ")?;
                line_loc = 2;
            }
            let value = self.values.get(&signal.1).unwrap().bits;
            write!(result, " {}={:0hex_width$x}", name, value, hex_width=hex_width)?;
            line_loc += 2 + hex_width + name.len();
        }
        if line_loc + 2 >= max_loc {
            while line_loc < max_loc {
                write!(result, " ")?;
                line_loc += 1;
            }
            write!(result, " |\n| ")?;
            line_loc = 2;
        }
        write!(result, " }}")?;
        line_loc += 2;
        while line_loc < max_loc {
            write!(result, " ")?;
            line_loc += 1;
        }
        write!(result, " |\n")?;
        Ok(())
    }

    fn dump_custom_registers_y86<W: Write>(&self, result: &mut W) -> Result<(), Error> {
        let mut banks_by_letter: HashMap<char, &RegisterBank> = HashMap::new();
        if self.program.register_banks.len() == 0 {
            return Ok(());
        }
        for bank in &self.program.register_banks {
            let letter = bank.stall_signal.chars().last().unwrap();
            banks_by_letter.insert(letter, bank);
        }
        let order = ['P', 'F', 'D', 'E', 'M', 'W'];
        for letter in order.iter() {
            if let Some(bank) = banks_by_letter.get(letter) {
                self.dump_bank(result, bank)?;
            }
        }
        for letter in order.iter() {
            banks_by_letter.remove(letter);
        }
        let mut letters: Vec<char> = banks_by_letter.keys().map(|&x| x).collect();
        letters.sort();
        for letter in letters {
            let bank = banks_by_letter.get(&letter).unwrap();
            self.dump_bank(result, bank)?;
        }
        Ok(())
    }

    pub fn name_status_y86(&self) -> &'static str {
        let status = self.status_or_default(255);
        if (status as usize) < Y86_STATUSES.len() {
            Y86_STATUSES[status as usize]
        } else {
            "<unknown>"
        }
    }

    pub fn dump_y86<W: Write>(&self, result: &mut W) -> Result<(), Error> {
        if self.halted() {
            writeln!(result,
                "+----------------------- halted in state: ------------------------------+"
            )?;
        } else if self.timed_out() {
            writeln!(result,
                "+------------ timed out after {:5} cycles in state: -------------------+",
                self.cycle
            )?;
        } else if self.done() {
            writeln!(result,
                "+------------------- error caused in state: ----------------------------+"
            )?;
        } else {
            writeln!(result,
                "+------------------- between cycles {:4} and {:4} ----------------------+",
                self.cycle, self.cycle + 1
            )?;
        }
        self.dump_program_registers_y86(result)?;
        if self.options.show_register_banks_with_registers {
            self.dump_custom_registers_y86(result)?;
        }
        self.memory.dump_memory_y86(result)?;
        if self.halted() {
            writeln!(result,
                "+--------------------- (end of halted state) ---------------------------+"
            )?;
        } else if self.done() && !self.timed_out() {
            writeln!(result,
                "+-------------------- (end of error state) -----------------------------+"
            )?;
        } else {
            writeln!(result,
                "+-----------------------------------------------------------------------+"
            )?;
        }
        if self.done() && !self.timed_out() {
            writeln!(result, "Cycles run: {}", self.cycle)?;
            if !self.halted() && !self.timed_out() {
                writeln!(result, "Error code: {}", self.name_status_y86())?;
            }
        }
        Ok(())
    }

    pub fn dump_y86_str(&self) -> String {
        let mut result: Vec<u8> = Vec::new();
        self.dump_y86(&mut result).expect("unexpected error while dumping state");
        String::from_utf8_lossy(result.as_slice()).into_owned()
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use ::tests::init_logger;
    use ast::{WireWidth, WireValue};

    use std::fmt::Debug;
    use std::hash::Hash;
    use std::collections::hash_set::HashSet;

    fn verify_sort<T: Eq + Clone + Hash + Debug>(graph: &Graph<T>) {
        match graph.topological_sort() {
            Ok(the_result) => {
                let mut seen = HashSet::new();
                for node in &the_result {
                    for other in graph.out_edges(&node) {
                        assert!(!seen.contains(&other), "{:?} -> {:?} violates order {:?}",
                            node, other, the_result);
                    }
                    seen.insert(node.clone());
                }
            },
            Err(the_cycle) => {
                assert!(the_cycle.len() > 0);
                for i in 0..the_cycle.len() {
                    assert!(graph.contains_edge(
                        &the_cycle[i],
                        &the_cycle[(i+1) % the_cycle.len()]
                    ));
                }
            }
        }
    }


    #[test]
    fn graph_sorts() {
        init_logger();
        let mut graph = Graph::new();
        graph.insert("foo", "bar");
        graph.insert("bar", "baz");
        verify_sort(&graph);
        graph.insert("foo", "baz");
        verify_sort(&graph);
        graph.insert("foo", "quux");
        graph.insert("quux", "other");
        verify_sort(&graph);
        graph.add_node("unused");
        verify_sort(&graph);
    }

    #[test]
    fn graph_simple_cycle() {
        init_logger();
        let mut graph = Graph::new();
        graph.insert("foo", "bar");
        graph.insert("bar", "baz");
        graph.insert("baz", "foo");
        verify_sort(&graph);
        graph.add_node("unused");
        verify_sort(&graph);
        graph.insert("baz", "quux");
        verify_sort(&graph);
        graph.insert("bar", "foo");
        verify_sort(&graph);
    }

    #[test]
    fn graph_3cycle() {
        init_logger();
        let mut graph = Graph::new();
        graph.insert("foo", "bar");
        graph.insert("bar", "baz");
        graph.insert("baz", "foo");
        verify_sort(&graph);
        graph.add_node("unused");
        verify_sort(&graph);
        graph.insert("baz", "quux");
        verify_sort(&graph);
        graph.insert("bar", "foo");
        verify_sort(&graph);
    }

    #[test]
    fn graph_2cycle() {
        init_logger();
        let mut graph = Graph::new();
        graph.insert("foo", "bar");
        graph.insert("bar", "foo");
        verify_sort(&graph);
        graph.insert("bar", "baz");
        verify_sort(&graph);
        graph.add_node("unused");
        verify_sort(&graph);
        graph.insert("baz", "quux");
        verify_sort(&graph);
    }

    #[test]
    fn graph_complex_cycle() {
        init_logger();
        let mut graph = Graph::new();
        graph.insert("root", "A1");
        graph.insert("A1", "A2");
        graph.insert("A2", "A3");
        graph.insert("root", "B1");
        graph.insert("B1", "B2");
        graph.insert("B2", "B3");
        graph.insert("B3", "A1");
        graph.insert("A1", "B2");
    }

    #[test]
    fn graph_self_cycle() {
        init_logger();
        let mut graph = Graph::new();
        graph.insert("foo", "foo");
        verify_sort(&graph);
        graph.insert("foo", "bar");
        graph.insert("bar", "baz");
        verify_sort(&graph);
    }

    #[test]
    fn memory_ops() {
        init_logger();
        let mut memory = Memory::new();
        assert_eq!(
            memory.read(0, 8),
            WireValue { bits: 0, width: WireWidth::Bits(64) }
        );
        assert_eq!(
            memory.read(1, 8),
            WireValue { bits: 0, width: WireWidth::Bits(64) }
        );
        assert_eq!(
            memory.read(9, 4),
            WireValue { bits: 0, width: WireWidth::Bits(32) }
        );
        memory.write(1, 0x0123456789ABCDEF, 8);
        assert_eq!(
            memory.read(5, 4),
            WireValue { bits: 0x01234567, width: WireWidth::Bits(32) }
        );
        assert_eq!(
            memory.read(3, 2),
            WireValue { bits: 0x89AB, width: WireWidth::Bits(16) }
        );
    }

}
