# Tiger-Cranelift

Tiger-Cranelift is a Tiger language implementation using [cranelift](https://github.com/bytecodealliance/cranelift). This project is intended to be yet another demo of cranelift.  
The compiler emits native binaries using cranelift-object backend.  
You can also find official cranelift-jit example [simplejit-demo](https://github.com/bytecodealliance/simplejit-demo).  

## Implementation Summary

### Parsing
Simple hand-written recursive descent parser. So there is nothing to saying about parsing phase.

### Semantic Analysis
Tiger language allows to define nested functions though closure is not allowed.  
In order to resolve nested functions, I adopted lambda-lifting because it make easier to build Cranelift IR in later.

### IR Building
All types in Tiger are lowered into ptr type of target machine to allow recursive type declaration like `type IntList = {head:int, tail: list}`.  
In semantic analysis phase all functions are lifted up to top-level functions, so IR building phase is quite straight forward.  

## Run
In the project root,
```
Cargo run file_path
```

### Compiler Options
```
USAGE:
    tigerc [FLAGS] [OPTIONS] <file>

FLAGS:
    -d               Also dump cranelift IR
    -h, --help       Prints help information
    -V, --version    Prints version information

OPTIONS:
    -O, --opt-level <level>    Specify optimization level [default: none]  [possible values: none, speed,
                               speed_and_size]
    -o <path>                  Place the output into <file> [default: ./a.out]

ARGS:
    <file> 
```

## Test
In the project root,
```
./test_all.sh
```

This command runs all unit tests + file tests.

## TODO
* [ ] Add error handling returned from cranelift.
* [ ] Add simple GC.
