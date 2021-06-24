extern crate env_logger;
use std::env;
use std::fs::File;
use std::io::{BufReader, Write, stdin, stdout, stderr};
use std::path::Path;

extern crate hclrs;
extern crate getopts;

use hclrs::*;

use getopts::Options;

fn main() {
    env_logger::init();
    let okay = main_real().unwrap();
    if okay {
        std::process::exit(0);
    } else {
        std::process::exit(1);
    }
}

fn parse_y86(file_contents: &FileContents) -> Result<RunningProgram, Error> {
    let program = parse_y86_hcl(file_contents)?;
    let running_program = RunningProgram::new_y86(program);
    Ok(running_program)
}

fn press_enter() {
    let mut input = String::new();
    println!("(press enter to continue)");
    stdin().read_line(&mut input).unwrap();
}

fn run_y86<W: Write>(mut running_program: RunningProgram, yo_path: &Path,
           run_options: RunOptions, out: &mut W) -> Result<(), Error> {
    let mut yo_reader = BufReader::new(File::open(yo_path)?);
    running_program.load_memory_y86(&mut yo_reader)?;
    running_program.set_options(run_options);
    running_program.run(out)?;
    print!("{}", running_program.dump_y86_str());
    Ok(())
}

fn print_usage(program_name: &str, opts: Options) { 
    let header = format!("Usage: {} [options] HCL-FILE [YO-FILE [TIMEOUT]]\n\
                          Runs HCL_FILE on YO-FILE. If --check is specified, no YO-FILE may be supplied.\n\
                          Default timeout is 9999 cycles.",
        program_name);
    print!("{}", opts.usage(&header));
}

const VERSION: &'static str = env!("CARGO_PKG_VERSION");

fn main_real() -> Result<bool, Error> {
    let args: Vec<String> = env::args().collect();
    let program_name = args[0].clone();
    let mut opts = Options::new();
    let mut run_options = RunOptions::default();
    opts.optflag("c", "check", "check syntax only");
    opts.optflag("d", "debug", "output wire values after each cycle and other debug output");
    opts.optflag("q", "quiet", "only output state at the end");
    opts.optflag("t", "testing", "do not output custom register banks (for autograding)");
    opts.optflag("h", "help", "print this help menu");
    opts.optflag("i", "interactive", "prompt after each cycle");
    opts.optflag("", "trace-assignments", "show assignments in the order they are simulated");
    opts.optflag("", "parse-file", "parse hcl file ");
    opts.optflag("", "version", "print version number");
    let parsed_opts = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            writeln!(stderr(), "{}", f.to_string()).unwrap();
            return Ok(false);
        }
    };
    if parsed_opts.opt_present("h") {
        print_usage(&program_name, opts);
        return Ok(true);
    }
    if parsed_opts.opt_present("version") {
        println!("HCLRS version {}", VERSION);
        return Ok(true);
    }
    if parsed_opts.opt_present("q") {
        run_options.set_quiet();
    }
    if parsed_opts.opt_present("d") {
        run_options.set_debug();
    }
    if parsed_opts.opt_present("t") {
        run_options.set_test();
    }
    if parsed_opts.opt_present("i") {
        run_options.set_prompt(Box::new(press_enter));
    }
    let check_only = parsed_opts.opt_present("c");
    let parse_file = parsed_opts.opt_present("parse-file");
    let free_args = parsed_opts.free;
    if free_args.len() < 1 {
        print_usage(&program_name, opts);
        return Ok(false);
    }
    let filename: &str = &free_args[0];
    let path = Path::new(filename);
    let file_contents = match read_y86_hcl(path) {
        Err(e) => {
            writeln!(stderr(), "Error reading '{}': {}", path.display(), e).unwrap();
            return Ok(false)
        },
        Ok(contents) => contents
    };
    if free_args.len() > 3 {
        print_usage(&program_name, opts);
        return Ok(false);
    }
    let running_program =
        match parse_y86(&file_contents) {
            Err(e) => {
                e.format_for_contents(&mut stderr(), &file_contents)?;
                return Ok(false);
            },
            Ok(p) => p,
        };
    if check_only {
        println!("syntax OK");
        return Ok(true);
    }
    if parse_file  {
        
        let t = running_program.parse_file_non_pipeline();
        println!("output assigned to pc is {} and the register with this wire is {}",t.0,t.1 );
        for wiretag_mark in t.2{
           println!("the wire {} is gotten from wire  {} and bytes {} to {}", wiretag_mark.get_to(),wiretag_mark.get_from(),wiretag_mark.get_low(),wiretag_mark.get_high()); 
        }
        running_program.print_all_registers();
        running_program.print_all_muxes();
        running_program.print_all_wire_assignments();
        return Ok(true);
    }
    if free_args.len() < 2 || free_args.len() > 3 {
        print_usage(&program_name, opts);
        return Ok(false);
    }
    let yo_filename: &str = &free_args[1];
    if !yo_filename.ends_with(".yo") {
        writeln!(stderr(), "'{}' does not have the extension .yo", yo_filename).unwrap();
        return Ok(false);
    }
    let timeout = 
        if free_args.len() > 2 {
            match u32::from_str_radix(&free_args[2], 10) {
                Ok(x) => x,
                Err(_) => {
                    writeln!(stderr(), "timeout {} is not a valid number", &free_args[2]).unwrap();
                    return Ok(false);
                }
            }
        } else {
            9999
        };
    run_options.set_timeout(timeout);
    let yo_path = Path::new(yo_filename);
    match run_y86(running_program, yo_path, run_options, &mut stdout()) {
        Err(e) => {
            e.format_for_contents(&mut stderr(), &file_contents)?;
            return Ok(false);
        },
        _ => {},
    }
    Ok(true)
}

