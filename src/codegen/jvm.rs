use core::ffi::*;
use core::mem::zeroed;
use crate::nob::*;
use crate::crust::libc::*;
use crate::{Op, Binop, OpWithLocation, Arg, Func, Global, ImmediateValue, Compiler, missingf, AsmFunc, Loc};

const CONSTANT_UTF8:        u8 = 1;
const CONSTANT_INTEGER:     u8 = 3;
const CONSTANT_LONG:        u8 = 5;
const CONSTANT_CLASS:       u8 = 7;
const CONSTANT_STRING:      u8 = 8;
const CONSTANT_METHODREF:   u8 = 10;
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
    Integer { value: i32 },
    Long { value: i64 },
    Class { name_index: u16 },
    String { string_index: u16 },
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
        CpInfo::Integer { value } => {
            write_byte(output, CONSTANT_INTEGER);
            write_dword(output, value as u32);
        }
        CpInfo::Long { value } => {
            write_byte(output, CONSTANT_LONG);
            write_dword(output, (value >> 32) as u32);
            write_dword(output, value as u32);
        }
        CpInfo::Class { name_index} => {
            write_byte(output, CONSTANT_CLASS);
            write_word(output, name_index);
        }
        CpInfo::String { string_index } => {
            write_byte(output, CONSTANT_STRING);
            write_word(output, string_index);
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
        Arg::External(name)     => printf(c!("ext %s"), name),
        Arg::Deref(index)       => printf(c!("deref[%zu]"), index),
        Arg::RefAutoVar(index)  => printf(c!("ref auto[%zu]"), index),
        Arg::RefExternal(name)  => printf(c!("ref %s"), name),
        Arg::Literal(value)     => printf(c!("const %ld"), value),
        Arg::AutoVar(index)     => printf(c!("auto[%zu]"), index),
        Arg::DataOffset(offset) => printf(c!("data[%zu]"), offset),
        Arg::Bogus              => unreachable!("bogus-amogus")
    };
}

#[derive(Clone, Copy, PartialEq)]
pub enum ArgType{
    Uninitialized,
    Integer,
    Long,
    String
}

const MAX_I32: u64 = i32::MAX as u64 + 1;
const MAX_I64: u64 = i64::MAX as u64;

pub unsafe fn load_arg_value(arg: Arg, output: *mut String_Builder, loc: Loc, gen: *mut Generator, local_types: *mut Array<ArgType>) -> ArgType{
    /*for i in 0..(*local_types).count{
        match *(*local_types).items.add(i) {
            ArgType::Integer       => printf(c!("L:   %zu Int\n"), i),
            ArgType::Long          => printf(c!("L:   %zu Long\n"), i),
            ArgType::Uninitialized => printf(c!("L:   %zu None\n"), i),
        };
    }
    printf(c!("\n"));*/
    match arg {
        Arg::Literal(value) => {
            match value {
                v @ 0..=5 => {
                    write_byte(output, 0x03 + v as u8); //iconst_0 + v
                    ArgType::Integer
                }
                v @ 6..MAX_I32 => {
                    write_byte(output, 0x12); //ldc
                    let value_index = get_or_create_cp_info_index(gen, CpInfo::Integer { value: v as i32 });
                    write_byte(output, value_index as u8);
                    ArgType::Integer
                }
                v @ MAX_I32..=MAX_I64 => {
                    write_byte(output, 0x14); //ldc2_w
                    let value_index = get_or_create_cp_info_index(gen, CpInfo::Long { value: v as i64 });
                    write_word(output, value_index);
                    ArgType::Long
                }
                _ => missingf!(loc, c!("jvm-auto-assign literals larger than i64::max are not supported by the jvm\n")),
            }
        },
        Arg::AutoVar(index) => {
            let auto_var_type = *(*local_types).items.add(index-1);
            match auto_var_type {
                ArgType::Integer => {
                    if index-1 <= 3{
                        write_byte(output, (0x1a + index - 1) as u8); //iload_0
                    } else {
                        write_byte(output, 0x15); //iload
                        write_byte(output, (index - 1) as u8); //iload index
                    }
                }
                ArgType::Long => {
                    if index-1 <= 3{
                        write_byte(output, (0x1e + index - 1) as u8); //lload_0
                    } else {
                        write_byte(output, 0x16); //lload
                        write_byte(output, (index - 1) as u8); //lload index
                    }
                }
                ArgType::String => {
                    if index-1 <= 3{
                        write_byte(output, (0x2a + index - 1) as u8); //aload_0
                    } else {
                        write_byte(output, 0x19); //aload
                        write_byte(output, (index - 1) as u8); //aload index
                    }
                }
                ArgType::Uninitialized => unreachable!("reading of uninitialized auto var at {}", index)
            }
            auto_var_type
        }
        Arg::External(_) => missingf!(loc, c!("loading args of type Arg::External is not supported yet\n")),
        Arg::Deref(_) => missingf!(loc, c!("loading args of type Arg::Deref is not supported yet\n")),
        Arg::RefAutoVar(_) => missingf!(loc, c!("loading args of type Arg::RefAutoVar is not supported yet\n")),
        Arg::RefExternal(_) => missingf!(loc, c!("loading args of type Arg::RefExternal is not supported yet\n")),
        Arg::DataOffset(offset) => {
            for i in 0..(*gen).strings.count{
                let (data_offset, string_index) = *(*gen).strings.items.add(i);
                if data_offset == offset{
                    write_byte(output, 0x12); //ldc
                    write_byte(output, string_index as u8);
                }
            }
            //missingf!(loc, c!("loading args of type Arg::DataOffset is not supported yet\n")),
            ArgType::String
        }
        Arg::Bogus => unreachable!("bogus-amogus"),
    }
}

//auto_var_index is before we subtract 1
pub unsafe fn store_value(auto_var_index: usize, output: *mut String_Builder, loc: Loc, arg_type: ArgType, local_types: *mut Array<ArgType>) {
    match arg_type {
        ArgType::Integer => {
            if auto_var_index-1 <= 3{
                printf(temp_sprintf(c!("istore_%zu\n"), auto_var_index-1));
                write_byte(output, 0x3b + (auto_var_index - 1) as u8) //istore_0 + index
            } else {
                printf(temp_sprintf(c!("istore %zu\n"), auto_var_index-1));
                write_byte(output, 0x36); //istore
                write_byte(output, (auto_var_index - 1) as u8); //istore index
            }
            *(*local_types).items.add(auto_var_index-1) = ArgType::Integer
        }
        ArgType::Long => {
            //storing of long values requires calculation of index offsets, because long takes two slots in locals and stack
            missingf!(loc, c!("storing of long values not safe yet"));
            if auto_var_index-1 <= 3{
                printf(temp_sprintf(c!("lstore_%zu\n"), auto_var_index-1));
                write_byte(output, 0x3f + (auto_var_index - 1) as u8) //lstore_0 + index
            } else {
                printf(temp_sprintf(c!("lstore %zu\n"), auto_var_index-1));
                write_byte(output, 0x37); //lstore
                write_byte(output, (auto_var_index - 1) as u8); //lstore index
            }
            *(*local_types).items.add(auto_var_index-1) = ArgType::Long
        }
        ArgType::String => {
            if auto_var_index-1 <= 3{
                printf(temp_sprintf(c!("astore_%zu\n"), auto_var_index-1));
                write_byte(output, 0x4b + (auto_var_index - 1) as u8) //astore_0 + index
            } else {
                printf(temp_sprintf(c!("astore %zu\n"), auto_var_index-1));
                write_byte(output, 0x3a); //astore
                write_byte(output, (auto_var_index - 1) as u8); //astore index
            }
        }
        ArgType::Uninitialized => unreachable!("storing uninitialized arg type is not possible")
    }
}

pub struct Generator{
    constant_pool: Array<CpInfo>,
    functions: Array<String_Builder>,
    //(offset, constant_pool_index)
    strings: Array<(usize, u16)>,
}

pub unsafe fn generate_function(name: *const c_char, params_count: usize, auto_vars_count: usize, body: *const [OpWithLocation], gen: *mut Generator) {
    printf(c!("%s(%zu, %zu):\n"), name, params_count, auto_vars_count);
    let mut info: String_Builder = zeroed();
    let mut locals_types: Array<ArgType> = zeroed();
    for _ in 0..auto_vars_count {
        da_append(&mut locals_types, ArgType::Uninitialized);
    }

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
            Op::Binop { binop, index, lhs, rhs } => {
                printf(c!("index: %zu, lhs: "), index);
                dump_arg(lhs);
                printf(c!(", rhs: "));
                dump_arg(rhs);
                printf(c!("\n"));

                let _lhs_arg_type = load_arg_value(lhs, &mut code, op.loc, gen, &mut locals_types);
                let _rhs_arg_type = load_arg_value(rhs, &mut code, op.loc, gen, &mut locals_types);
                match binop {
                    Binop::Plus => {
                        //TODO match types
                        write_byte(&mut code, 0x60); //iadd
                        store_value(index, &mut code, op.loc, ArgType::Integer, &mut locals_types);
                    }
                    _ => missingf!(op.loc, c!("binop of this type is not supported yet\n")),
                }
            },
            Op::AutoAssign { index, arg} => {
                printf(c!("[%zu] = "), index);
                dump_arg(arg);
                printf(c!("\n"));
                let arg_type = load_arg_value(arg, &mut code, op.loc, gen, &mut locals_types);

                store_value(index, &mut code, op.loc, arg_type, &mut locals_types);
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

pub unsafe fn generate_funcs(funcs: *const [Func], gen: *mut Generator) {
    printf(c!("-- Functions --\n"));
    printf(c!("\n"));
    for i in 0..funcs.len() {
        generate_function((*funcs)[i].name, (*funcs)[i].params_count, (*funcs)[i].auto_vars_count, da_slice((*funcs)[i].body), gen);
    }
}

pub unsafe fn generate_strings_from_data_section(output: *mut String_Builder, data: *const [u8], gen: *mut Generator){
    let mut buffer: Array<c_char> = zeroed();
    let mut data_offset = 0;
    for i in 0..data.len(){
        let c: u8 = (*data)[i];
        da_append(&mut buffer, c as c_char);
        if c == b'\0'{
            let utf_index = get_or_create_cp_info_index(gen, CpInfo::Utf8 { value: da_slice(buffer) as *const c_char });
            let string_index = get_or_create_cp_info_index(gen, CpInfo::String { string_index: utf_index });
            da_append(&mut (*gen).strings, (data_offset, string_index));
            buffer = zeroed();
            data_offset = i + 1;
        }
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
    //TODO try to create the constant pool entries at the spot they are needed
    generate_strings_from_data_section(output, da_slice((*c).data), &mut gen);
    generate_funcs(da_slice((*c).funcs), &mut gen);
    generate_body(output, &mut gen);
}