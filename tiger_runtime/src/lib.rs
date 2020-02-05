use std::ffi;
use std::io::{self, Read, Write};

#[no_mangle]
fn print(s: *const i8) {
    let s = unsafe { ffi::CStr::from_ptr(s) };
    print!("{}", s.to_str().unwrap());
}

#[no_mangle]
fn println(s: *const i8) {
    let s = unsafe { ffi::CStr::from_ptr(s) };
    println!("{}", s.to_str().unwrap());
}

#[no_mangle]
fn print_int(i: isize) {
    println!("{}", i);
}

#[no_mangle]
fn flush() {
    io::stdout().flush().ok();
}

#[no_mangle]
fn getchar() -> *const i8 {
    let c = io::stdin().bytes().next().unwrap().unwrap() as i8;
    let s = alloc_string(1);
    unsafe { *s = c };
    s
}

#[no_mangle]
fn ord(i: *const i8) -> isize {
    if size(i) == 0 {
        -1
    } else {
        unsafe { i.read() as isize }
    }
}

#[no_mangle]
fn chr(i: isize) -> *const i8 {
    let s = alloc_string(1);
    unsafe { *s = i as i8 };
    s
}

#[no_mangle]
fn substring(s: *const i8, first: isize, n: isize) -> *const i8 {
    if first + n >= size(s) {
        panic!("Index outof range");
    }

    let subs = alloc(n);
    unsafe { s.add(first as usize).copy_to(subs, n as usize) };
    subs
}

#[no_mangle]
fn concat(s1: *const i8, s2: *const i8) -> *const i8 {
    let s1_size = size(s1);
    let s2_size = size(s2);
    let concatted = alloc_string(size(s1) + size(s2));
    unsafe {
        s1.copy_to(concatted, s1_size as usize);
        s2.copy_to(concatted.add(s1_size as usize), s2_size as usize);
    }
    concatted
}

#[no_mangle]
fn size(s: *const i8) -> isize {
    unsafe { ffi::CStr::from_ptr(s).to_bytes().len() as isize }
}

#[no_mangle]
fn not(i: isize) -> isize {
    (i == 0) as isize
}

#[no_mangle]
fn exit(i: isize) {
    std::process::exit(i as i32)
}

#[no_mangle]
fn alloc(size: isize) -> *mut i8 {
    let mut v = Vec::with_capacity(size as usize);
    let ptr = v.as_mut_ptr();
    std::mem::forget(v);
    ptr
}

#[no_mangle]
fn init_array(size: isize, value: isize) -> *mut isize {
    let unit = std::mem::size_of::<isize>() as isize;
    let arr = alloc(size * unit) as *mut isize;
    for i in 0..size {
        unsafe {
            *arr.add(i as usize) = value;
        }
    }
    arr
}

#[no_mangle]
fn alloc_string(len: isize) -> *mut i8 {
    let p = alloc(len + 1);
    unsafe { *p.add(len as usize) = 0 };
    p
}
