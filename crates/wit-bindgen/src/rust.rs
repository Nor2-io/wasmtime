use crate::{types::TypeInfo, Ownership};
use heck::*;
use std::collections::HashMap;
use std::fmt::Write;
use wit_parser::*;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum TypeMode {
    Owned,
    AllBorrowed(&'static str),
}

pub trait RustGenerator<'a> {
    fn resolve(&self) -> &'a Resolve;

    fn push_str(&mut self, s: &str);
    fn info(&self, ty: TypeId) -> TypeInfo;
    fn path_to_interface(&self, interface: InterfaceId) -> Option<String>;

    /// This determines whether we generate owning types or (where appopriate)
    /// borrowing types.
    ///
    /// For example, when generating a type which is only used as a parameter to
    /// a guest-exported function, there is no need for it to own its fields.
    /// However, constructing deeply-nested borrows (e.g. `&[&[&[&str]]]]` for
    /// `list<list<list<string>>>`) can be very awkward, so by default we
    /// generate owning types and use only shallow borrowing at the top level
    /// inside function signatures.
    fn ownership(&self) -> Ownership;

    fn print_ty(&mut self, ty: &Type, mode: TypeMode) {
        self.push_str(&self.print_ty_(ty, mode));
    }

    #[must_use]
    fn print_ty_(&self, ty: &Type, mode: TypeMode) -> String {
        match ty {
            Type::Id(t) => self.print_tyid_(*t, mode),
            Type::Bool => "bool".to_owned(),
            Type::U8 => "u8".to_owned(),
            Type::U16 => "u16".to_owned(),
            Type::U32 => "u32".to_owned(),
            Type::U64 => "u64".to_owned(),
            Type::S8 => "i8".to_owned(),
            Type::S16 => "i16".to_owned(),
            Type::S32 => "i32".to_owned(),
            Type::S64 => "i64".to_owned(),
            Type::Float32 => "f32".to_owned(),
            Type::Float64 => "f64".to_owned(),
            Type::Char => "char".to_owned(),
            Type::String => match mode {
                TypeMode::AllBorrowed(lt) => {
                    let mut out: String = "&".to_owned();
                    if lt != "'_" {
                        out.push_str(lt);
                        out.push_str(" ");
                    }
                    out.push_str("str");

                    out
                }
                TypeMode::Owned => "String".to_owned(),
            },
        }
    }

    fn print_optional_ty(&mut self, ty: Option<&Type>, mode: TypeMode) {
        self.push_str(&self.print_optional_ty_(ty, mode));
    }

    #[must_use]
    fn print_optional_ty_(&self, ty: Option<&Type>, mode: TypeMode) -> String {
        match ty {
            Some(ty) => self.print_ty_(ty, mode),
            None => "()".to_owned(),
        }
    }

    fn print_tyid(&mut self, id: TypeId, mode: TypeMode) {
        self.push_str(&self.print_tyid_(id, mode));
    }

    #[must_use]
    fn print_tyid_(&self, id: TypeId, mode: TypeMode) -> String {
        let info = self.info(id);
        let lt = self.lifetime_for(&info, mode);
        let ty = &self.resolve().types[id];

        let mut out = String::default();

        if ty.name.is_some() {
            // If this type has a list internally, no lifetime is being printed,
            // but we're in a borrowed mode, then that means we're in a borrowed
            // context and don't want ownership of the type but we're using an
            // owned type definition. Inject a `&` in front to indicate that, at
            // the API level, ownership isn't required.
            if info.has_list && lt.is_none() {
                if let TypeMode::AllBorrowed(lt) = mode {
                    out.push_str("&");
                    if lt != "'_" {
                        out.push_str(lt);
                        out.push_str(" ");
                    }
                }
            }
            let name = if lt.is_some() {
                self.param_name(id)
            } else {
                self.result_name(id)
            };
            if let TypeOwner::Interface(id) = ty.owner {
                if let Some(path) = self.path_to_interface(id) {
                    out.push_str(&path);
                    out.push_str("::");
                }
            }
            out.push_str(&name);

            // If the type recursively owns data and it's a
            // variant/record/list, then we need to place the
            // lifetime parameter on the type as well.
            if info.has_list && needs_generics(self.resolve(), &ty.kind) {
                if let Some(generics) = self.print_generics_(lt) {
                    out.push_str(&generics);
                }
            }

            return out;

            fn needs_generics(resolve: &Resolve, ty: &TypeDefKind) -> bool {
                match ty {
                    TypeDefKind::Variant(_)
                    | TypeDefKind::Record(_)
                    | TypeDefKind::Option(_)
                    | TypeDefKind::Result(_)
                    | TypeDefKind::Future(_)
                    | TypeDefKind::Stream(_)
                    | TypeDefKind::List(_)
                    | TypeDefKind::Flags(_)
                    | TypeDefKind::Enum(_)
                    | TypeDefKind::Tuple(_)
                    | TypeDefKind::Union(_)
                    | TypeDefKind::Handle(_)
                    | TypeDefKind::Resource => true,
                    TypeDefKind::Type(Type::Id(t)) => {
                        needs_generics(resolve, &resolve.types[*t].kind)
                    }
                    TypeDefKind::Type(Type::String) => true,
                    TypeDefKind::Type(_) => false,
                    TypeDefKind::Unknown => unreachable!(),
                }
            }
        }

        match &ty.kind {
            TypeDefKind::List(t) => out.push_str(&self.print_list_(t, mode)),

            TypeDefKind::Option(t) => {
                out.push_str("Option<");
                out.push_str(&self.print_ty_(t, mode));
                out.push_str(">");
            }

            TypeDefKind::Result(r) => {
                out.push_str("Result<");
                out.push_str(&self.print_optional_ty_(r.ok.as_ref(), mode));
                out.push_str(",");
                out.push_str(&self.print_optional_ty_(r.err.as_ref(), mode));
                out.push_str(">");
            }

            TypeDefKind::Variant(_) => panic!("unsupported anonymous variant"),

            // Tuple-like records are mapped directly to Rust tuples of
            // types. Note the trailing comma after each member to
            // appropriately handle 1-tuples.
            TypeDefKind::Tuple(t) => {
                out.push_str("(");
                for ty in t.types.iter() {
                    out.push_str(&self.print_ty_(ty, mode));
                    out.push_str(",");
                }
                out.push_str(")");
            }
            TypeDefKind::Resource => {
                panic!("unsupported anonymous type reference: resource")
            }
            TypeDefKind::Record(_) => {
                panic!("unsupported anonymous type reference: record")
            }
            TypeDefKind::Flags(_) => {
                panic!("unsupported anonymous type reference: flags")
            }
            TypeDefKind::Enum(_) => {
                panic!("unsupported anonymous type reference: enum")
            }
            TypeDefKind::Union(_) => {
                panic!("unsupported anonymous type reference: union")
            }
            TypeDefKind::Future(ty) => {
                out.push_str("Future<");
                out.push_str(&self.print_optional_ty_(ty.as_ref(), mode));
                out.push_str(">");
            }
            TypeDefKind::Stream(stream) => {
                out.push_str("Stream<");
                out.push_str(&self.print_optional_ty_(stream.element.as_ref(), mode));
                out.push_str(",");
                out.push_str(&self.print_optional_ty_(stream.end.as_ref(), mode));
                out.push_str(">");
            }
            TypeDefKind::Handle(Handle::Own(ty)) => {
                //TODO: Clean up how resource types are outputted
                out.push_str("wasmtime::component::ResourceAny");
                //self.push_str("wasmtime::component::Resource<Rep");
                //self.print_tyid(*ty, mode);
                //self.push_str(">");
            }
            TypeDefKind::Handle(Handle::Borrow(ty)) => {
                //TODO: Clean up how resource types are outputted
                out.push_str("wasmtime::component::ResourceAny");
                //self.push_str("wasmtime::component::Resource<Rep");
                //self.print_tyid(*ty, mode);
                //self.push_str(">");
            }
            TypeDefKind::Type(t) => out.push_str(&self.print_ty_(t, mode)),
            TypeDefKind::Unknown => unreachable!(),
        }

        out
    }

    fn print_list(&mut self, ty: &Type, mode: TypeMode) {
        self.push_str(&self.print_list_(ty, mode));
    }

    #[must_use]
    fn print_list_(&self, ty: &Type, mode: TypeMode) -> String {
        let next_mode = if matches!(self.ownership(), Ownership::Owning) {
            TypeMode::Owned
        } else {
            mode
        };
        match mode {
            TypeMode::AllBorrowed(lt) => {
                let mut out = "&".to_owned();

                if lt != "'_" {
                    out.push_str(lt);
                    out.push_str(" ");
                }
                out.push_str("[");
                out.push_str(&self.print_ty_(ty, next_mode));
                out.push_str("]");

                out
            }
            TypeMode::Owned => {
                format!("Vec<{}>", self.print_ty_(ty, next_mode))
            }
        }
    }

    fn print_generics(&mut self, lifetime: Option<&str>) {
        if let Some(lt) = self.print_generics_(lifetime) {
            self.push_str(&lt);
        }
    }

    #[must_use]
    fn print_generics_(&self, lifetime: Option<&str>) -> Option<String> {
        if lifetime.is_none() {
            return None;
        }
        let mut out = "<".to_owned();

        if let Some(lt) = lifetime {
            out.push_str(lt);
            out.push_str(",");
        }
        out.push_str(">");

        Some(out)
    }

    fn modes_of(&self, ty: TypeId) -> Vec<(String, TypeMode)> {
        let info = self.info(ty);
        if !info.owned && !info.borrowed {
            return Vec::new();
        }
        let mut result = Vec::new();
        let first_mode =
            if info.owned || !info.borrowed || matches!(self.ownership(), Ownership::Owning) {
                TypeMode::Owned
            } else {
                assert!(!self.uses_two_names(&info));
                TypeMode::AllBorrowed("'a")
            };
        result.push((self.result_name(ty), first_mode));
        if self.uses_two_names(&info) {
            result.push((self.param_name(ty), TypeMode::AllBorrowed("'a")));
        }
        result
    }

    /// Writes the camel-cased 'name' of the passed type to `out`, as used to name union variants.
    fn write_name(&self, ty: &Type, out: &mut String) {
        match ty {
            Type::Bool => out.push_str("Bool"),
            Type::U8 => out.push_str("U8"),
            Type::U16 => out.push_str("U16"),
            Type::U32 => out.push_str("U32"),
            Type::U64 => out.push_str("U64"),
            Type::S8 => out.push_str("I8"),
            Type::S16 => out.push_str("I16"),
            Type::S32 => out.push_str("I32"),
            Type::S64 => out.push_str("I64"),
            Type::Float32 => out.push_str("F32"),
            Type::Float64 => out.push_str("F64"),
            Type::Char => out.push_str("Char"),
            Type::String => out.push_str("String"),
            Type::Id(id) => {
                let ty = &self.resolve().types[*id];
                match &ty.name {
                    Some(name) => out.push_str(&name.to_upper_camel_case()),
                    None => match &ty.kind {
                        TypeDefKind::Option(ty) => {
                            out.push_str("Optional");
                            self.write_name(ty, out);
                        }
                        TypeDefKind::Result(_) => out.push_str("Result"),
                        TypeDefKind::Tuple(_) => out.push_str("Tuple"),
                        TypeDefKind::List(ty) => {
                            self.write_name(ty, out);
                            out.push_str("List")
                        }
                        TypeDefKind::Future(ty) => {
                            self.write_optional_name(ty.as_ref(), out);
                            out.push_str("Future");
                        }
                        TypeDefKind::Stream(s) => {
                            self.write_optional_name(s.element.as_ref(), out);
                            self.write_optional_name(s.end.as_ref(), out);
                            out.push_str("Stream");
                        }

                        TypeDefKind::Type(ty) => self.write_name(ty, out),
                        TypeDefKind::Record(_) => out.push_str("Record"),
                        TypeDefKind::Flags(_) => out.push_str("Flags"),
                        TypeDefKind::Variant(_) => out.push_str("Variant"),
                        TypeDefKind::Enum(_) => out.push_str("Enum"),
                        TypeDefKind::Union(_) => out.push_str("Union"),
                        TypeDefKind::Handle(Handle::Own(ty)) => {
                            self.write_name(&Type::Id(*ty), out);
                            out.push_str("Own");
                        }
                        TypeDefKind::Handle(Handle::Borrow(ty)) => {
                            self.write_name(&Type::Id(*ty), out);
                            out.push_str("Borrow");
                        }
                        TypeDefKind::Resource => out.push_str("Resource"),
                        TypeDefKind::Unknown => unreachable!(),
                    },
                }
            }
        }
    }

    fn write_optional_name(&self, ty: Option<&Type>, out: &mut String) {
        match ty {
            Some(ty) => self.write_name(ty, out),
            None => out.push_str("()"),
        }
    }

    /// Returns the names for the cases of the passed union.
    fn union_case_names(&self, union: &Union) -> Vec<String> {
        enum UsedState<'a> {
            /// This name has been used once before.
            ///
            /// Contains a reference to the name given to the first usage so that a suffix can be added to it.
            Once(&'a mut String),
            /// This name has already been used multiple times.
            ///
            /// Contains the number of times this has already been used.
            Multiple(usize),
        }

        // A `Vec` of the names we're assigning each of the union's cases in order.
        let mut case_names = vec![String::new(); union.cases.len()];
        // A map from case names to their `UsedState`.
        let mut used = HashMap::new();
        for (case, name) in union.cases.iter().zip(case_names.iter_mut()) {
            self.write_name(&case.ty, name);

            match used.get_mut(name.as_str()) {
                None => {
                    // Initialise this name's `UsedState`, with a mutable reference to this name
                    // in case we have to add a suffix to it later.
                    used.insert(name.clone(), UsedState::Once(name));
                    // Since this is the first (and potentially only) usage of this name,
                    // we don't need to add a suffix here.
                }
                Some(state) => match state {
                    UsedState::Multiple(n) => {
                        // Add a suffix of the index of this usage.
                        write!(name, "{n}").unwrap();
                        // Add one to the number of times this type has been used.
                        *n += 1;
                    }
                    UsedState::Once(first) => {
                        // Add a suffix of 0 to the first usage.
                        first.push('0');
                        // We now get a suffix of 1.
                        name.push('1');
                        // Then update the state.
                        *state = UsedState::Multiple(2);
                    }
                },
            }
        }

        case_names
    }

    fn param_name(&self, ty: TypeId) -> String {
        let info = self.info(ty);
        let name = self.resolve().types[ty]
            .name
            .as_ref()
            .unwrap()
            .to_upper_camel_case();
        if self.uses_two_names(&info) {
            format!("{}Param", name)
        } else {
            name
        }
    }

    fn result_name(&self, ty: TypeId) -> String {
        let info = self.info(ty);
        let name = self.resolve().types[ty]
            .name
            .as_ref()
            .unwrap()
            .to_upper_camel_case();
        if self.uses_two_names(&info) {
            format!("{}Result", name)
        } else {
            name
        }
    }

    fn uses_two_names(&self, info: &TypeInfo) -> bool {
        info.has_list
            && info.borrowed
            && info.owned
            && matches!(
                self.ownership(),
                Ownership::Borrowing {
                    duplicate_if_necessary: true
                }
            )
    }

    fn lifetime_for(&self, info: &TypeInfo, mode: TypeMode) -> Option<&'static str> {
        if matches!(self.ownership(), Ownership::Owning) {
            return None;
        }
        let lt = match mode {
            TypeMode::AllBorrowed(s) => s,
            _ => return None,
        };
        // No lifetimes needed unless this has a list.
        if !info.has_list {
            return None;
        }
        // If two names are used then this type will have an owned and a
        // borrowed copy and the borrowed copy is being used, so it needs a
        // lifetime. Otherwise if it's only borrowed and not owned then this can
        // also use a lifetime since it's not needed in two contexts and only
        // the borrowed version of the structure was generated.
        if self.uses_two_names(info) || (info.borrowed && !info.owned) {
            Some(lt)
        } else {
            None
        }
    }
}

/// Translate `name` to a Rust `snake_case` identifier.
pub fn to_rust_ident(name: &str) -> String {
    match name {
        // Escape Rust keywords.
        // Source: https://doc.rust-lang.org/reference/keywords.html
        "as" => "as_".into(),
        "break" => "break_".into(),
        "const" => "const_".into(),
        "continue" => "continue_".into(),
        "crate" => "crate_".into(),
        "else" => "else_".into(),
        "enum" => "enum_".into(),
        "extern" => "extern_".into(),
        "false" => "false_".into(),
        "fn" => "fn_".into(),
        "for" => "for_".into(),
        "if" => "if_".into(),
        "impl" => "impl_".into(),
        "in" => "in_".into(),
        "let" => "let_".into(),
        "loop" => "loop_".into(),
        "match" => "match_".into(),
        "mod" => "mod_".into(),
        "move" => "move_".into(),
        "mut" => "mut_".into(),
        "pub" => "pub_".into(),
        "ref" => "ref_".into(),
        "return" => "return_".into(),
        "self" => "self_".into(),
        "static" => "static_".into(),
        "struct" => "struct_".into(),
        "super" => "super_".into(),
        "trait" => "trait_".into(),
        "true" => "true_".into(),
        "type" => "type_".into(),
        "unsafe" => "unsafe_".into(),
        "use" => "use_".into(),
        "where" => "where_".into(),
        "while" => "while_".into(),
        "async" => "async_".into(),
        "await" => "await_".into(),
        "dyn" => "dyn_".into(),
        "abstract" => "abstract_".into(),
        "become" => "become_".into(),
        "box" => "box_".into(),
        "do" => "do_".into(),
        "final" => "final_".into(),
        "macro" => "macro_".into(),
        "override" => "override_".into(),
        "priv" => "priv_".into(),
        "typeof" => "typeof_".into(),
        "unsized" => "unsized_".into(),
        "virtual" => "virtual_".into(),
        "yield" => "yield_".into(),
        "try" => "try_".into(),
        s => s.to_snake_case(),
    }
}

/// Translate `name` to a Rust `UpperCamelCase` identifier.
pub fn to_rust_upper_camel_case(name: &str) -> String {
    match name {
        // We use `Host` as the name of the trait for host implementations
        // to fill in, so rename it if "Host" is used as a regular identifier.
        "host" => "Host_".into(),
        s => s.to_upper_camel_case(),
    }
}
