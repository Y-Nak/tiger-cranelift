// TODO: Handle error.
use std::collections::HashMap;
use std::fs;
use std::io::{BufWriter, Write};

use cranelift::prelude::*;
use cranelift_module::{DataContext, FuncId, Linkage, Module as ClifModule};
use cranelift_object::{ObjectBackend, ObjectBuilder, ObjectProduct};

use target_lexicon::Triple;

use crate::ast;
use crate::impl_prelude::*;
use crate::prelude::Opts;
use crate::symbol_table::SymbolTable;

type Module = ClifModule<ObjectBackend>;

pub struct CodeGen {
    module: Module,
    builder_ctx: FunctionBuilderContext,
    func_ctx: codegen::Context,
    func_env: FuncEnv,
    global_env: GlobalEnv,
    opts: Opts,
    ir: String,
}

impl CodeGen {
    pub fn new(opts: Opts) -> Self {
        let mut flag_builder = codegen::settings::builder();
        flag_builder.set("opt_level", &opts.opt_level).unwrap();

        let flag = codegen::settings::Flags::new(codegen::settings::builder());

        // Target isa is same as host machine.
        let isa = codegen::isa::lookup(Triple::host()).unwrap().finish(flag);

        let builder = ObjectBuilder::new(
            isa,
            "".into(),
            cranelift_object::ObjectTrapCollection::Disabled,
            cranelift_module::default_libcall_names(),
        )
        .unwrap();

        let module = Module::new(builder);
        let func_ctx = module.make_context();
        let mut gen = Self {
            module,
            builder_ctx: FunctionBuilderContext::new(),
            func_ctx,
            func_env: HashMap::new(),
            global_env: HashMap::new(),
            opts,
            ir: String::new(),
        };

        gen.prefill_builtin_functions();
        gen
    }

    pub fn gen_code(mut self, funcs: &[ast::Function]) -> ObjectProduct {
        for func in funcs {
            self.define_function(func);
        }
        self.module.finalize_definitions();
        if self.opts.dump_clif {
            self.dump_ir();
        }
        self.module.finish()
    }

    fn define_function(&mut self, func: &ast::Function) {
        let func_id = self.declare_function(func.name, &func.args, &func.ret_ty, Linkage::Export);

        let builder = FunctionBuilder::new(&mut self.func_ctx.func, &mut self.builder_ctx);
        let mut translator = FunctionTranslator::new(
            &mut self.module,
            builder,
            &self.func_env,
            &mut self.global_env,
        );
        translator.translate_func(&func);

        self.module
            .define_function(func_id, &mut self.func_ctx)
            .unwrap();

        if self.opts.dump_clif {
            self.ir.push_str(&format!("{}\n", self.func_ctx.func));
        }

        self.module.clear_context(&mut self.func_ctx);
    }

    fn declare_function(
        &mut self,
        name: Symbol,
        args: &[(Symbol, Ty)],
        ret_ty: &Ty,
        linkage: Linkage,
    ) -> FuncId {
        self.translate_signature(args, ret_ty);
        let clif_func_id = self
            .module
            .declare_function(name.as_str(), linkage, &self.func_ctx.func.signature)
            .unwrap();
        self.func_env.insert(name, clif_func_id);
        clif_func_id
    }

    fn translate_signature(&mut self, args: &[(Symbol, Ty)], ret_ty: &Ty) {
        for (_, arg_ty) in args.iter() {
            let abi_param = AbiParam::new(translate_ty(arg_ty, &self.module).unwrap());
            self.func_ctx.func.signature.params.push(abi_param);
        }

        if let Some(clif_ty) = translate_ty(&ret_ty, &self.module) {
            let abi_param = AbiParam::new(clif_ty);
            self.func_ctx.func.signature.returns.push(abi_param);
        }
    }

    fn prefill_builtin_functions(&mut self) {
        self.prefill_func("print", &[TyKind::String_], TyKind::Unit);
        self.prefill_func("println", &[TyKind::String_], TyKind::Unit);
        self.prefill_func("print_int", &[TyKind::Int], TyKind::Unit);
        self.prefill_func("flush", &[], TyKind::Unit);
        self.prefill_func("getchar", &[], TyKind::String_);
        self.prefill_func("ord", &[TyKind::String_], TyKind::Int);
        self.prefill_func("chr", &[TyKind::Int], TyKind::String_);
        self.prefill_func(
            "substring",
            &[TyKind::String_, TyKind::Int, TyKind::Int],
            TyKind::String_,
        );
        self.prefill_func(
            "concat",
            &[TyKind::String_, TyKind::String_],
            TyKind::String_,
        );
        self.prefill_func("size", &[TyKind::String_], TyKind::Int);
        self.prefill_func("not", &[TyKind::Int], TyKind::Int);
        self.prefill_func("exit", &[TyKind::Int], TyKind::Unit);

        self.prefill_func("alloc", &[TyKind::Int], TyKind::Nil);
        self.prefill_func("init_array", &[TyKind::Nil, TyKind::Nil], TyKind::Nil);
    }

    fn prefill_func(&mut self, name: &str, args: &[TyKind], ret_ty: TyKind) {
        let args: Vec<(Symbol, Ty)> = args
            .into_iter()
            .map(|kind| (Symbol::intern("dummy"), Ty::new(kind.clone(), Pos::dummy())))
            .collect();
        let ret_ty = Ty::new(ret_ty, Pos::dummy());
        self.declare_function(Symbol::intern(name), &args, &ret_ty, Linkage::Import);
        self.module.clear_context(&mut self.func_ctx);
    }

    fn dump_ir(&self) {
        let output_path = &self.opts.output_path;
        let file_name = format!(
            "{}.clif",
            output_path.file_stem().unwrap().to_str().unwrap()
        );
        let ir_output_path = output_path.with_file_name(file_name);
        let file = fs::File::create(ir_output_path).unwrap();
        let mut buf_writer = BufWriter::new(file);
        buf_writer.write_all(self.ir.as_bytes()).unwrap();
    }
}

struct FunctionTranslator<'a> {
    module: &'a mut Module,
    builder: FunctionBuilder<'a>,
    value_env: ValueEnv,
    loop_env: Vec<Block>,
    func_env: &'a FuncEnv,
    global_env: &'a mut GlobalEnv,
    ptr_type: Type,
    variable_id: usize,
}

impl<'a> FunctionTranslator<'a> {
    fn new(
        module: &'a mut Module,
        builder: FunctionBuilder<'a>,
        func_env: &'a FuncEnv,
        global_env: &'a mut GlobalEnv,
    ) -> Self {
        let ptr_type = module.target_config().pointer_type();
        Self {
            module,
            builder,
            value_env: ValueEnv::new(),
            loop_env: Vec::new(),
            func_env,
            global_env,
            ptr_type,
            variable_id: 0,
        }
    }

    fn translate_func(&mut self, func: &ast::Function) {
        // Create first block of function.
        let func_entry = self.builder.create_block();

        // Handle function parameters.
        self.builder
            .append_block_params_for_function_params(func_entry);
        self.builder.seal_block(func_entry);
        self.builder.switch_to_block(func_entry);
        for (i, (name, _)) in func.args.iter().enumerate() {
            let var = self.new_variable(*name);
            self.builder
                .def_var(var, self.builder.block_params(func_entry)[i]);
        }

        // Translate body.
        let value = self.translate_expr(&func.body);
        if func.ret_ty.kind == TyKind::Unit {
            self.builder.ins().return_(&[]);
        } else {
            self.builder.ins().return_(&[value]);
        }
        self.builder.finalize();
    }

    fn translate_expr(&mut self, expr: &ast::Expr) -> Value {
        match &expr.kind {
            ast::ExprKind::BinOp { lhs, rhs, kind } => self.translate_binop(lhs, rhs, *kind),
            ast::ExprKind::UnOp { lhs, kind } => self.translate_unop(lhs, *kind),
            ast::ExprKind::Lit(lit) => self.translate_literal(*lit),
            ast::ExprKind::Call { name, args } => self.translate_call(*name, args),
            ast::ExprKind::Record { fields, .. } => self.translate_record(fields),
            ast::ExprKind::Array { size, init, .. } => self.translate_array(size, init),
            ast::ExprKind::If {
                cond,
                then,
                else_: Some(else_),
            } => self.translate_if_else(cond, then, else_),
            ast::ExprKind::If {
                cond,
                then,
                else_: None,
            } => self.translate_if(cond, then),
            ast::ExprKind::While { cond, body } => self.translate_while(cond, body),
            ast::ExprKind::For {
                var,
                from,
                to,
                body,
            } => self.translate_for(*var, from, to, body),
            ast::ExprKind::Let { decls, body } => self.translate_let(decls, body),
            ast::ExprKind::Break => self.translate_break(),
            ast::ExprKind::ExprSeq(seq) => {
                let mut result = self.null();
                for expr in seq.iter() {
                    result = self.translate_expr(expr);
                }
                result
            }
            ast::ExprKind::Var(var) => {
                let var = self.value_env.look(*var).unwrap();
                self.builder.use_var(*var)
            }
            ast::ExprKind::FieldAccess { lvalue, field } => {
                self.translate_field_access(lvalue, *field)
            }
            ast::ExprKind::Index { lvalue, index } => self.translate_index(lvalue, index),
            ast::ExprKind::Assign { lvalue, rhs } => self.translate_assign(lvalue, rhs),
        }
    }

    fn translate_binop(&mut self, lhs: &ast::Expr, rhs: &ast::Expr, kind: ast::BinOpKind) -> Value {
        use ast::BinOpKind;
        let ptr_type = self.ptr_type;
        match kind {
            BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div => {
                let (lhs, rhs) = (self.translate_expr(lhs), self.translate_expr(rhs));
                match kind {
                    BinOpKind::Add => self.builder.ins().iadd(lhs, rhs),
                    BinOpKind::Sub => self.builder.ins().isub(lhs, rhs),
                    BinOpKind::Mul => self.builder.ins().imul(lhs, rhs),
                    BinOpKind::Div => self.builder.ins().sdiv(lhs, rhs),
                    _ => unreachable!(),
                }
            }

            BinOpKind::Eq_
            | BinOpKind::Ne
            | BinOpKind::Lt
            | BinOpKind::Le
            | BinOpKind::Gt
            | BinOpKind::Ge => {
                let (lhs, rhs) = (self.translate_expr(lhs), self.translate_expr(rhs));
                let cmp_flag = match kind {
                    BinOpKind::Eq_ => IntCC::Equal,
                    BinOpKind::Lt => IntCC::SignedLessThan,
                    BinOpKind::Le => IntCC::SignedLessThanOrEqual,
                    BinOpKind::Gt => IntCC::SignedGreaterThan,
                    BinOpKind::Ge => IntCC::SignedGreaterThanOrEqual,
                    _ => unreachable!(),
                };
                let result = self.builder.ins().icmp(cmp_flag, lhs, rhs);
                self.builder.ins().bint(ptr_type, result)
            }

            BinOpKind::LogicalAnd => self.translate_logical_expr(lhs, rhs, true),
            BinOpKind::LogicalOr => self.translate_logical_expr(lhs, rhs, false),
        }
    }

    fn translate_unop(&mut self, lhs: &ast::Expr, kind: ast::UnOpKind) -> Value {
        let lhs = self.translate_expr(lhs);
        match kind {
            ast::UnOpKind::Minus => self.builder.ins().ineg(lhs),
        }
    }

    fn translate_literal(&mut self, lit: ast::LitKind) -> Value {
        match lit {
            ast::LitKind::Num(symbol) => {
                let num: i64 = symbol.as_str().parse().unwrap();
                self.builder.ins().iconst(self.ptr_type, num)
            }
            ast::LitKind::Nil => self.null(),
            ast::LitKind::LitStr(s) => {
                let str_ptr = if let Some(str_ptr) = self.global_env.get(&s) {
                    *str_ptr
                } else {
                    let label = format!(".LS{}", s.as_usize());
                    let data_id = self
                        .module
                        .declare_data(&label, Linkage::Local, false, None)
                        .unwrap();
                    let mut data_ctx = DataContext::new();
                    data_ctx.define(s.as_str().to_owned().into_boxed_str().into());
                    self.module.define_data(data_id, &data_ctx).unwrap();
                    let str_ptr = self.module.declare_data_in_func(data_id, self.builder.func);
                    self.global_env.insert(s, str_ptr);
                    str_ptr
                };
                self.builder.ins().global_value(self.ptr_type, str_ptr)
            }
        }
    }

    fn translate_call(&mut self, name: Symbol, args: &[ast::Expr]) -> Value {
        let mut arg_values = Vec::new();
        for arg in args {
            arg_values.push(self.translate_expr(arg));
        }

        let func_id = self.func_env.get(&name).unwrap();
        let func_ref = self
            .module
            .declare_func_in_func(*func_id, &mut self.builder.func);
        let inst = self.builder.ins().call(func_ref, &arg_values);
        if self.builder.inst_results(inst).is_empty() {
            self.builder.ins().iconst(self.ptr_type, 0)
        } else {
            self.builder.inst_results(inst)[0]
        }
    }

    fn translate_record(&mut self, fields: &[(Symbol, ast::Expr)]) -> Value {
        let size = (fields.len() * self.ptr_type.bytes() as usize) as i64;
        let size = self.builder.ins().iconst(self.ptr_type, size as i64);

        let alloc_id = self.func_env.get(&Symbol::intern("alloc")).unwrap();
        let alloc_ref = self
            .module
            .declare_func_in_func(*alloc_id, &mut self.builder.func);
        let inst = self.builder.ins().call(alloc_ref, &[size]);
        let record = self.builder.inst_results(inst)[0];

        for (i, (_, expr)) in fields.iter().enumerate() {
            let value = self.translate_expr(expr);
            let offset = (i * self.ptr_type.bytes() as usize) as i32;
            self.builder
                .ins()
                .store(MemFlags::new(), value, record, offset);
        }
        record
    }

    fn translate_array(&mut self, size: &ast::Expr, init: &ast::Expr) -> Value {
        let size = self.translate_expr(size);
        let init = self.translate_expr(init);
        let array_bytes = self
            .builder
            .ins()
            .imul_imm(size, self.ptr_type.bytes() as i64);

        let init_array_id = self.func_env.get(&Symbol::intern("init_array")).unwrap();
        let init_array_ref = self
            .module
            .declare_func_in_func(*init_array_id, &mut self.builder.func);
        let inst = self
            .builder
            .ins()
            .call(init_array_ref, &[array_bytes, init]);
        self.builder.inst_results(inst)[0]
    }

    fn translate_if_else(
        &mut self,
        cond: &ast::Expr,
        then: &ast::Expr,
        else_: &ast::Expr,
    ) -> Value {
        let then_bb = self.builder.create_block();
        let else_bb = self.builder.create_block();
        let merge_bb = self.builder.create_block();
        self.builder.append_block_param(merge_bb, self.ptr_type);

        let cond = self.translate_expr(cond);
        self.builder.ins().brz(cond, else_bb, &[]);
        self.builder.ins().jump(then_bb, &[]);

        self.builder.seal_block(else_bb);
        self.builder.seal_block(then_bb);

        self.builder.switch_to_block(then_bb);
        let value = self.translate_expr(then);
        self.builder.ins().jump(merge_bb, &[value]);

        self.builder.switch_to_block(else_bb);
        let value = self.translate_expr(else_);
        self.builder.ins().jump(merge_bb, &[value]);

        self.builder.seal_block(merge_bb);
        self.builder.switch_to_block(merge_bb);
        self.builder.block_params(merge_bb)[0]
    }

    fn translate_if(&mut self, cond: &ast::Expr, then: &ast::Expr) -> Value {
        let then_bb = self.builder.create_block();
        let merge_bb = self.builder.create_block();

        let cond = self.translate_expr(cond);
        self.builder.ins().brz(cond, merge_bb, &[]);
        self.builder.ins().jump(then_bb, &[]);

        self.builder.seal_block(then_bb);
        self.builder.switch_to_block(then_bb);
        self.translate_expr(then);
        self.builder.ins().jump(merge_bb, &[]);

        self.builder.seal_block(merge_bb);
        self.builder.switch_to_block(merge_bb);
        self.null()
    }

    fn translate_while(&mut self, cond: &ast::Expr, body: &ast::Expr) -> Value {
        let header_bb = self.builder.create_block();
        let body_bb = self.builder.create_block();
        let end_bb = self.builder.create_block();

        self.builder.ins().jump(header_bb, &[]);
        self.builder.switch_to_block(header_bb);

        let cond = self.translate_expr(cond);
        self.builder.ins().brz(cond, end_bb, &[]);
        self.builder.ins().jump(body_bb, &[]);

        self.loop_env.push(end_bb);
        self.builder.seal_block(body_bb);
        self.builder.switch_to_block(body_bb);
        self.translate_expr(body);
        self.builder.ins().jump(header_bb, &[]);
        self.loop_env.pop();

        self.builder.seal_block(header_bb);
        self.builder.seal_block(end_bb);
        self.builder.switch_to_block(end_bb);
        self.null()
    }

    fn translate_for(
        &mut self,
        var: Symbol,
        from: &ast::Expr,
        to: &ast::Expr,
        body: &ast::Expr,
    ) -> Value {
        self.value_env.enter_scope();
        let header_bb = self.builder.create_block();
        let body_bb = self.builder.create_block();
        let end_bb = self.builder.create_block();

        let var = self.new_variable(var);
        let from = self.translate_expr(from);
        let to = self.translate_expr(to);
        self.builder.def_var(var, from);
        self.builder.ins().jump(header_bb, &[]);

        self.builder.switch_to_block(header_bb);
        let var_val = self.builder.use_var(var);
        self.builder
            .ins()
            .br_icmp(IntCC::SignedGreaterThanOrEqual, var_val, to, end_bb, &[]);
        self.builder.ins().jump(body_bb, &[]);

        self.loop_env.push(end_bb);
        self.builder.seal_block(body_bb);
        self.builder.switch_to_block(body_bb);
        self.translate_expr(body);
        let var_val = self.builder.use_var(var);
        let new_var_val = self.builder.ins().iadd_imm(var_val, 1);
        self.builder.def_var(var, new_var_val);
        self.builder.ins().jump(header_bb, &[]);
        self.loop_env.pop();

        self.builder.seal_block(header_bb);
        self.builder.seal_block(end_bb);
        self.builder.switch_to_block(end_bb);
        self.value_env.exit_scope();
        self.null()
    }

    fn translate_let(&mut self, decls: &[ast::Decl], body: &ast::Expr) -> Value {
        self.value_env.enter_scope();
        for decl in decls {
            if let ast::DeclKind::VarDec(var_dec) = &decl.kind {
                let var = self.new_variable(var_dec.name);
                let val = self.translate_expr(&var_dec.init);
                self.builder.def_var(var, val);
            }
        }

        let value = self.translate_expr(body);
        self.value_env.exit_scope();
        value
    }

    fn translate_break(&mut self) -> Value {
        let end_bb = self.loop_env.last().unwrap();
        self.builder.ins().jump(*end_bb, &[]);

        let new_bb = self.builder.create_block();
        self.builder.seal_block(new_bb);
        self.builder.switch_to_block(new_bb);
        self.null()
    }

    fn translate_logical_expr(&mut self, lhs: &ast::Expr, rhs: &ast::Expr, is_and: bool) -> Value {
        let b1 = self.builder.create_block();
        let merge_bb = self.builder.create_block();
        self.builder.append_block_param(merge_bb, self.ptr_type);

        let lhs = self.translate_expr(lhs);

        if is_and {
            self.builder.ins().brnz(lhs, b1, &[]);
        } else {
            self.builder.ins().brz(lhs, b1, &[]);
        }

        self.builder.ins().jump(merge_bb, &[lhs]);

        self.builder.seal_block(b1);
        self.builder.switch_to_block(b1);
        let rhs = self.translate_expr(rhs);
        self.builder.ins().jump(merge_bb, &[rhs]);

        self.builder.seal_block(merge_bb);
        self.builder.switch_to_block(merge_bb);
        self.builder.block_params(merge_bb)[0]
    }

    fn translate_field_access(&mut self, lvalue: &ast::Expr, field: Symbol) -> Value {
        let p = self.translate_expr(lvalue);
        let offset = self.offset_of_record(lvalue, field);
        self.builder
            .ins()
            .load(self.ptr_type, MemFlags::new(), p, offset)
    }

    fn translate_index(&mut self, lvalue: &ast::Expr, index: &ast::Expr) -> Value {
        let p = self.pointer_of_indexed_array(lvalue, index);
        self.builder
            .ins()
            .load(self.ptr_type, MemFlags::new(), p, 0)
    }

    fn translate_assign(&mut self, lvalue: &ast::Expr, rhs: &ast::Expr) -> Value {
        let rhs = self.translate_expr(rhs);

        match &lvalue.kind {
            ast::ExprKind::Var(name) => {
                let var = self.value_env.look(*name).unwrap();
                self.builder.def_var(*var, rhs);
            }
            ast::ExprKind::FieldAccess { lvalue, field } => {
                let p = self.translate_expr(lvalue);
                let offset = self.offset_of_record(lvalue, *field);
                self.builder.ins().store(MemFlags::new(), rhs, p, offset);
            }
            ast::ExprKind::Index { lvalue, index } => {
                let p = self.pointer_of_indexed_array(lvalue, index);
                self.builder.ins().store(MemFlags::new(), rhs, p, 0);
            }

            _ => unreachable!(),
        }
        rhs
    }

    fn pointer_of_indexed_array(&mut self, arr: &ast::Expr, index: &ast::Expr) -> Value {
        let lvalue = self.translate_expr(arr);
        let index = self.translate_expr(index);
        let offset = self
            .builder
            .ins()
            .imul_imm(index, self.ptr_type.bytes() as i64);
        self.builder.ins().iadd(lvalue, offset)
    }

    fn offset_of_record(&self, lvalue: &ast::Expr, field: Symbol) -> i32 {
        let record_field = lvalue.ty.kind.record_field_unchecked();
        let offset = record_field
            .iter()
            .position(|(name, _)| *name == field)
            .unwrap();
        (offset * self.ptr_type.bytes() as usize) as i32
    }

    fn new_variable(&mut self, name: Symbol) -> Variable {
        let var = Variable::new(self.variable_id);
        self.variable_id += 1;
        self.value_env.insert(name, var);
        let clif_ty = self.ptr_type;
        self.builder.declare_var(var, clif_ty);
        var
    }

    fn null(&mut self) -> Value {
        self.builder.ins().iconst(self.ptr_type, 0)
    }
}

type ValueEnv = SymbolTable<Variable>;
type FuncEnv = HashMap<Symbol, FuncId>;
type GlobalEnv = HashMap<Symbol, codegen::ir::GlobalValue>;

fn translate_ty(ty: &Ty, module: &Module) -> Option<types::Type> {
    match ty.kind {
        TyKind::Unit => None,
        TyKind::Invalid => panic!("Invalid type can't exist after sematic analysis"),
        _ => Some(module.target_config().pointer_type()),
    }
}
