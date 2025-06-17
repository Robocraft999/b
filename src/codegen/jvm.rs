use core::ffi::*;
use core::mem::zeroed;
use crate::nob::*;
use crate::crust::libc::*;
use crate::{Op, Binop, OpWithLocation, Arg, Func, Global, ImmediateValue, Compiler, missingf, AsmFunc};

const CONSTANT_UTF8: u8 = 1;
const CONSTANT_CLASS: u8 = 7;
const CONSTANT_METHODREF: u8 = 10;
const CONSTANT_NAMEANDTYPE: u8 = 12;

/*pub unsafe fn da_contains<T: PartialEq>(xs: *mut Array<T>, item: T) -> bool {
    for i in 0..(*xs).count{
        if *(*xs).items.add(i) == item {
            return true;
        }
    }
    return false;
}*/

pub unsafe fn da_index_of<T: PartialEq>(xs: *mut Array<T>, item: T) -> Option<usize> {
    for i in 0..(*xs).count{
        if *(*xs).items.add(i) == item {
            return Some(i);
        }
    }
    return None;
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq)]
pub enum CpInfo{
    Utf8 { value: *const c_char },
    Class { name_index: u16 },
    Methodref { class_index: u16, name_and_type_index: u16 },
    NameAndType { name_index: u16, type_index: u16 },
}

pub unsafe fn get_or_create_cp_info_index(gen: *mut Generator, info: CpInfo) -> u16{
    if let Some(index) = da_index_of(&mut (*gen).constant_pool, info){
        index as u16 + 1
    } else {
        da_append(&mut (*gen).constant_pool, info);
        (*gen).constant_pool.count as u16
    }
}

pub unsafe fn write_byte(output: *mut String_Builder, byte: u8) {
    da_append(output, byte as c_char);
}
pub unsafe fn write_word(output: *mut String_Builder, word: u16) {
    write_byte(output, (word >> 8) as u8);
    write_byte(output, word as u8);
}

pub unsafe fn write_dword(output: *mut String_Builder, word: u32) {
    write_byte(output, (word >> 24) as u8);
    write_byte(output, (word >> 16) as u8);
    write_byte(output, (word >> 8) as u8);
    write_byte(output, word as u8);
}

pub unsafe fn write_cp_info(output: *mut String_Builder, cp_info: CpInfo) {
    match cp_info {
        CpInfo::Utf8 { value} => {
            write_byte(output, CONSTANT_UTF8);
            write_word(output, strlen(value) as u16);
            sb_appendf(output, value);
        }
        CpInfo::Class { name_index} => {
            write_byte(output, CONSTANT_CLASS);
            write_word(output, name_index)
        }
        CpInfo::Methodref { class_index, name_and_type_index } => {
            write_byte(output, CONSTANT_METHODREF);
            write_word(output, class_index);
            write_word(output, name_and_type_index);
        }
        CpInfo::NameAndType { name_index, type_index } => {
            write_byte(output, CONSTANT_NAMEANDTYPE);
            write_word(output, name_index);
            write_word(output, type_index);
        }
    }
}

pub unsafe fn dump_arg(arg: Arg) {
    match arg {
        Arg::External(name)     => printf(c!("%s"), name),
        Arg::Deref(index)       => printf(c!("deref[%zu]"), index),
        Arg::RefAutoVar(index)  => printf(c!("ref auto[%zu]"), index),
        Arg::RefExternal(name)  => printf(c!("ref %s"), name),
        Arg::Literal(value)     => printf(c!("%ld"), value),
        Arg::AutoVar(index)     => printf(c!("auto[%zu]"), index),
        Arg::DataOffset(offset) => printf(c!("data[%zu]"), offset),
        Arg::Bogus              => unreachable!("bogus-amogus")
    };
}

pub struct Generator{
    constant_pool: Array<CpInfo>,
    functions: Array<String_Builder>,
}

pub unsafe fn generate_function(name: *const c_char, params_count: usize, auto_vars_count: usize, body: *const [OpWithLocation], output: *mut String_Builder, gen: *mut Generator) {
    printf(c!("%s(%zu, %zu):\n"), name, params_count, auto_vars_count);
    let mut info: String_Builder = zeroed();

    //access_flags
    write_word(&mut info, 0x0001 | 0x0008); //ACC_PUBLIC | ACC_STATIC

    let name_index = get_or_create_cp_info_index(gen, CpInfo::Utf8 {value: name});
    write_word(&mut info, name_index);

    let descriptor_index = get_or_create_cp_info_index(gen, CpInfo::Utf8 {value: c!("()V")});
    write_word(&mut info, descriptor_index);

    //attribute_count
    write_word(&mut info, 1);

    //Code attribute
    let code_name_index = get_or_create_cp_info_index(gen, CpInfo::Utf8 {value: c!("Code")});
    write_word(&mut info, code_name_index);

    let mut code: String_Builder = zeroed();
    for i in 0..body.len() {
        let op = (*body)[i];
        match op.opcode {
            Op::Bogus => unreachable!("bogus-amogus",),
            Op::UnaryNot { result: _, arg: _ } => missingf!(op.loc, c!("jvm-unary-not\n")),
            Op::Negate { result: _, arg: _ } => missingf!(op.loc, c!("jvm-negate\n")),
            Op::Asm { args: _ } => missingf!(op.loc, c!("jvm-asm\n")),
            Op::Binop { binop: _, index: _, lhs: _, rhs: _ } => missingf!(op.loc, c!("binop\n")),
            Op::AutoAssign { index, arg} => {
                printf(c!("[%zu] = "), index);
                dump_arg(arg);
                printf(c!("\n"));
                let value = match arg{
                    Arg::Literal(value) => value,
                    _ => missingf!(op.loc, c!("jvm-auto-assign arg type can not be handled\n"))
                };
                const max_i32: u64 = i32::MAX as u64 + 1;
                const max_i64: u64 = i64::MAX as u64;
                match value {
                    v @ 0..5 => {
                        printf(temp_sprintf(c!("iconst_%zu\n"), v));
                        write_byte(&mut code, 0x03 + v as u8); //iconst_0 + v
                        if index-1 <= 3{
                            printf(temp_sprintf(c!("istore_%zu\n"), index-1));
                            write_byte(&mut code, 0x3b + (index - 1) as u8) //istore_0 + index
                        } else {
                            printf(temp_sprintf(c!("istore %zu\n"), index-1));
                            write_byte(&mut code, 0x36); //istore
                            write_byte(&mut code, (index - 1) as u8); //istore index
                        }
                    }
                    v @ 6..max_i32 => {
                        printf(temp_sprintf(c!("ldc [] (%zu)\n"), v));
                        missingf!(op.loc, c!("jvm-auto-assign literals larger than 5 ar currently not supported\n"));
                    }
                    v @ max_i32..=max_i64 => {
                        printf(temp_sprintf(c!("ldc2_w [] (%zu)\n"), v));
                        missingf!(op.loc, c!("jvm-auto-assign literals larger than i32::max ar currently not supported\n"));
                    }
                    _ => missingf!(op.loc, c!("jvm-auto-assign literals larger than i64::max are not supported by the jvm")),
                }

            }
            Op::ExternalAssign {name: _, arg: _} => missingf!(op.loc, c!("jvm-external-assign\n")),
            Op::Store {index: _, arg: _} => missingf!(op.loc, c!("jvm-store\n")),
            Op::Funcall {result: _, fun: _, args: _} => {
                missingf!(op.loc, c!("jvm-funcall\n"))
            }
            Op::Label {label: _} => missingf!(op.loc, c!("jvm-label\n")),
            Op::JmpLabel { label: _} => missingf!(op.loc, c!("jvm-jmp-label\n")),
            Op::JmpIfNotLabel {label: _, arg: _} => missingf!(op.loc, c!("jvm-jmp-if-not-label\n")),
            Op::Return {arg: _} => missingf!(op.loc, c!("jvm-return\n")),
        }
    }
    let code_length = code.count;
    let attribute_length = (2 + 2 + 4 + code_length + 2 + 2) as u32;
    write_dword(&mut info, attribute_length); //attribute_length
    let max_locals = (params_count + auto_vars_count) as u16;
    write_word(&mut info, max_locals); //max_stack
    write_word(&mut info, max_locals); //max_locals
    write_dword(&mut info, code_length as u32);
    da_append_many(&mut info, da_slice(code));
    write_word(&mut info, 0); //exception_table_length
    write_word(&mut info, 0); //attributes_count

    da_append(&mut (*gen).functions, info);
}

pub unsafe fn generate_funcs(output: *mut String_Builder, funcs: *const [Func], gen: *mut Generator) {
    printf(c!("-- Functions --\n"));
    printf(c!("\n"));
    for i in 0..funcs.len() {
        generate_function((*funcs)[i].name, (*funcs)[i].params_count, (*funcs)[i].auto_vars_count, da_slice((*funcs)[i].body), output, gen);
    }
}

pub unsafe fn generate_header(output: *mut String_Builder) {
    write_dword(output, 0xCAFEBABE);
    write_word(output, 0);
    write_word(output, 51);
}

pub unsafe fn generate_body(output: *mut String_Builder, gen: *mut Generator) {

    let super_class_name = get_or_create_cp_info_index(gen, CpInfo::Utf8 {value: c!("java/lang/Object")});
    let super_class = get_or_create_cp_info_index(gen, CpInfo::Class {name_index: super_class_name});

    let this_class_name = get_or_create_cp_info_index(gen, CpInfo::Utf8 {value: c!("Hello")});
    let this_class = get_or_create_cp_info_index(gen, CpInfo::Class {name_index: this_class_name});

    //constantpool
    // "The value of the constant_pool_count item is equal to the number of entries in the constant_pool table plus one"
    let constant_pool_count = (*gen).constant_pool.count + 1;
    write_word(output, constant_pool_count as u16);
    let constant_pool = da_slice((*gen).constant_pool);
    // "The constant_pool table is indexed from 1 to constant_pool_count - 1"
    for i in 1..constant_pool_count {
        write_cp_info(output, (*constant_pool)[i-1]);
    }

    //access flags
    write_word(output, 0x0020); //ACC_SUPER

    write_word(output, this_class);
    write_word(output, super_class);

    //interfaces
    write_word(output, 0); //interfaces_count
    //write_interfaces

    //fields
    write_word(output, 0); //fields_count
    //write_fields

    //methods
    write_word(output, (*gen).functions.count as u16); //methods_count
    //write_methods
    let funcs = da_slice((*gen).functions);
    for i in 0..(*gen).functions.count {
        da_append_many(output, da_slice((*funcs)[i]));
    }

    //attributes
    write_word(output, 0); //attributes_count
    //write_attributes

}

pub unsafe fn generate_program(output: *mut String_Builder, c: *const Compiler) {
    let mut gen: Generator = zeroed();
    generate_header(output);
    generate_funcs(output, da_slice((*c).funcs), &mut gen);
    generate_body(output, &mut gen);
}