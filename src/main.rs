// We use error-chain to simplify the handling of errors in Rust. If you're not
// familiar with error-chain, see
// http://brson.github.io/2016/11/30/starting-with-error-chain
#[macro_use]
extern crate error_chain;

// Of course, we'll need falcon
extern crate falcon;

// Falcon uses the standard rust log crate. It's your preferene whether you want to
// see Falcon's logging output, but I do, so I always set this up.
extern crate log;

// Rayon is a, "Data-parallelism library for Rust." We use Rayon to simplify parallelizing
// Falcon, allowing us to step multiple symbolic executors forward simultaneously. Falcon
// is thread-safe and meets Rust's thread-safe guarantees.
extern crate rayon;

// The il module is used to create and modify Falcon IL directly.
// We use this module to create constraints and query a SymbolicEngine, as all
// state is represented in Falcon IL.
use falcon::il;

// The engine module contains everything needed for Symbolic Execution.
use falcon::engine;

// The loader module loads and links the Elfs we have provided, allowing
// us to bootstrap a SymbolicMemory, and lift functions. If needed, we could even
// attempt to lift an entire program across all Elfs with relocations pre-resolved.
use falcon::loader::Loader;

// The platform module models a system. We use the LinuxX86 platform. Currently LinuxX86
// only has two system calls modelled, read and write. Fortunately, this is enough
// for Palindrome.
use falcon::platform;

// We also need to use the Platform trait.
use falcon::platform::Platform;

// Requirements for the log crate.
use log::{LogRecord, LogLevel, LogLevelFilter, LogMetadata};

// We need rayon prelude for magical parallel iterators.
use rayon::prelude::*;

// We specify the path of the binary to load as a rust Path object.
use std::path::Path;

// We need to pass certain things wrapped in Arc to get our EngineDriver started.
use std::sync::Arc;


// Create our logger
struct StdoutLogger;

impl log::Log for StdoutLogger {
    fn enabled(&self, metadata: &LogMetadata) -> bool {
        metadata.level() <= LogLevel::Trace
    }

    fn log(&self, record: &LogRecord) {
        if self.enabled(record.metadata()) {
            println!("{} - {}", record.level(), record.args());
        }
    }
}


// Bootstrap error-chain
pub mod error {
    error_chain! {
        types {
            Error, ErrorKind, ResultExt, Result;
        }

        foreign_links {
            Falcon(::falcon::error::Error);
        }
    }
}

pub use error::*;



fn step_driver_to_address<P> (
    driver: engine::EngineDriver<P>,
    target_address: u64,
    steps_to_take: usize
) -> Result<Vec<engine::EngineDriver<P>>> where P: platform::Platform<P> + Send + Sync {

    let mut final_drivers = Vec::new();
    let mut drivers = vec![driver];

    for _ in 0..steps_to_take {
        if drivers.len() == 0 {
            break;
        }
        let mut step_drivers = Vec::new();
        for driver in drivers {
            if let Some(address) = driver.address() {
                if address == target_address {
                    final_drivers.push(driver);
                    continue;
                }
            }
            step_drivers.append(&mut driver.step()?);
        }
        drivers = step_drivers;
    }

    final_drivers.append(&mut drivers);

    Ok(final_drivers)
}



fn get_past_read<P>(driver: engine::EngineDriver<P>)
    -> Result<engine::EngineDriver<P>> where P: platform::Platform<P> + Send + Sync {

    // We keep track of the possible forked states in a Vec of EngineDriver.
    // We update this Vec in each iteration of the loop which follows.
    let mut drivers = vec![driver];

    loop {
        // step_drivers is a Vec of EngineDriver we want to continue stepping through.
        // Not adding an EngineDriver to step_drivers is equivalent to killing, or
        // terminating, that state.
        let mut step_drivers = Vec::new();

        for driver in drivers {
            // If the EngineDriver is currently executing an Instruction (as opposed to,
            // for eaxmple, a conditional edge), we can query the EngineDriver for the
            // address of the instruction being executed. This address is added by the
            // binary lifter, and is the address in memory the instruction was lifted
            // from.
            if let Some(address) = driver.address() {

                // We are going to check each state when it reaches address 0x8048800 
                if address == 0x8048800 {

                    // Get the eax scalar from the SymbolicEngine
                    let eax = driver.engine().get_scalar("eax").unwrap();

                    // We are going to ask the Engine to solve for a value of eax, while also
                    // providing a constraint that eax == 0x80. In the event there is a satisfiable
                    // value state where eax == 0x80, an il::Constant will be returned with the
                    // value of eax (which will be 0x80 because of our constraint).
                    //
                    // At this time in the program, eax is actually an il::Constant, and we could
                    // just fetch that constant, but the method below is more generic and will
                    // work for scalars which are also symbolic.
                    if let Some(eax) = driver.engine().eval(
                        eax,
                        Some(vec![il::Expression::cmpeq(il::expr_scalar("eax", 32), il::expr_const(0x80, 32))?])
                    )? {
                        // Double-check that eax is 0x80, and return this EngineDriver.
                        if eax.value() == 0x80 {
                            return Ok(driver.clone());
                        }
                    }
                }
                // We are returning from read_delim without having read enough
                // bytes. We, "Kill," this state by not adding it to the Vec of
                // states we will continue to step.
                else if address == 0x804880d {
                    continue
                }
            }
            // The current EngineDriver has not reached our desired condition at
            // 0x8048800, nor has it attempted to exit the function, so we continue
            // to step it forward.
            step_drivers.push(driver);
        }
        // into_par_iter() is a threaded, parallel iterator provided by rayon that
        // allows for simple multi-threading of operations when thread-safe guarantees
        // are met by code in Rust. Falcon meets these thread-safety guarantees, and
        // we can step through multiple drivers in a parallel fashion.
        //
        // We don't see much benefit using rayon in this particular function, but when
        // we have many states to step we see great performance improvements from
        // parallelization.
        drivers = step_drivers.into_par_iter()
                              .map(|d| d.step().unwrap())
                              .reduce(|| Vec::new(), |mut v, mut d| {
                                v.append(&mut d);
                                v
                            });

        // In the event we run out of drivers, all states have been terminated before
        // reaching our desired condition at 0x8048800. This is an error condition
        // for us.
        if drivers.len() == 0 {
            bail!("Ran out of drivers");
        }
    }
}



fn run () -> Result<()> {
    // Load our target binary
    let path = Path::new("Palindrome/Palindrome");
    let elf = falcon::loader::elf::ElfLinker::new(&path)?;

    // Create one function in our program at the entry to this Elf. We need to
    // do this so we can create a valid ProgramLocation.
    let mut program = il::Program::new();
    program.add_function(elf.function(elf.program_entry())?);

    // Get a valid ProgramLocation for this Elf.
    let program_location = engine::ProgramLocation::from_address(elf.program_entry(), &program).unwrap();

    // Create a new `SymbolicMemory`
    let mut memory = engine::SymbolicMemory::new(engine::Endian::Little);

    // Copy over, one byte at a time, the memory from our Loader into the `SymbolicMemory`.
    for (address, segment) in elf.memory()?.segments() {
        let bytes = segment.bytes();
        for i in 0..bytes.len() {
            memory.store(*address + i as u64, il::expr_const(bytes[i] as u64, 8))?;
        }
    }

    // Create a new SymbolicEngine, passing it our initial memory model.
    let mut engine = engine::SymbolicEngine::new(memory);

    // Create a new LinuxX86 platform.
    let mut platform = platform::LinuxX86::new();

    // Initialize both the LinuxX86 platform, and the SymbolicEngine, together.
    platform.initialize(&mut engine)?;

    // Get the architecture translator from the loader so our EngineDriver can
    // opportunistically lift new code.
    let translator = elf.translator()?;

    // Create our EngineDriver.
    let driver = engine::EngineDriver::new(
        Arc::new(program),
        program_location,
        engine,
        &translator,
        Arc::new(platform)
    );

    // Get past the receive() function in receive_delim.
    let driver = get_past_read(driver)?;

    println!("Past read");

    // We only want to take one state back to the check function.
    let drivers = step_driver_to_address(driver, 0x804880e, 256)?;

    println!("End of read_delim");

    let driver = drivers[0].clone();

    // Step until we hit the return address of the check function.
    let drivers = step_driver_to_address(driver, 0x80489ce, 256)?;

    println!("Hit return address in check");

    // We only need one state.
    let driver = drivers[0].clone();

    // Get the address of the stack pointer. This is an il::Constant.
    let esp = driver.engine().get_scalar_only_concrete("esp")?.unwrap();
    
    // Read a 32-bit dword from symbolic memory at the stack pointer.
    let retaddr = driver.engine().memory().load(esp.value(), 32)?.unwrap();

    // Print out the stack pointer, and memory pointed to by the stack pointer.
    println!("{} {}", esp, retaddr);

    // Convenience reference to this EngineDriver's SymbolicEngine
    let engine = driver.engine();

    // Create a constraint that the expression we found for the return address will be
    // equal to 0xdeadbeef.
    let constraint = Some(vec![il::Expression::cmpeq(retaddr, il::expr_const(0xdeadbeef, 32))?]);

    // We get the symbolic_scalars from our platform. This will return all symbolic scalars created
    // from symbolic reads in order. This is convenient for us, as we only read from stdin, so we
    // will receive an in-order Vec of scalars for each byte of input read over stdin.
    let scalars = driver.platform().symbolic_scalars();

    // Solve for a valid value of each symbolic byte of input while enforcing the
    // constraint that the return address is equal to 0xdeadbeef.
    let values = scalars.iter()
                        .map(|s| engine.eval(&s.clone().into(), constraint.clone()).unwrap().unwrap())
                        .collect::<Vec<il::Constant>>();

    // Create a nicely formatted string we can copy and paste elsewhere.
    let input = values.iter()
                      .map(|v| format!("\\x{:02x}", v.value()))
                      .collect::<Vec<String>>()
                      .join("");

    // Print out our solved-for inputs.
    println!("{}", input);

    Ok(())
}



fn main () {
    // Initialize the log crate
    log::set_logger(|max_log_level| {
        max_log_level.set(LogLevelFilter::Trace);
        Box::new(StdoutLogger)
    }).unwrap();

    // error-chain boilerplate.
    if let Err(ref e) = run() {
        println!("error: {}", e);

        for e in e.iter().skip(1) {
            println!("caused by: {}", e);
        }

        // Print out a backtrace if we've generated one.
        if let Some(backtrace) = e.backtrace() {
            println!("backtrace: {:?}", backtrace);
        }

        ::std::process::exit(1);
    }
}