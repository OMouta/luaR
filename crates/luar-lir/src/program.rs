//! A whole program in LIR: its types, its functions, and where it starts.

use std::collections::BTreeMap;

use luar_diagnostics::Span;

use crate::inst::{Inst, Terminator, Value};
use crate::ty::{Ty, TypeId};

/// A function in the program. Stable for the life of the [`Program`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncId(pub u32);

/// A block in one function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(pub u32);

/// A stack slot in one function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SlotId(pub u32);

/// One field of a struct or of an enum variant's payload.
#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub name: String,
    pub ty: Ty,
}

/// A struct (LR12.2).
#[derive(Debug, Clone, PartialEq)]
pub struct Struct {
    /// Fields in declaration order. That order is what `MakeStruct` takes and
    /// what `GetField` indexes; it is not the order in memory, which the
    /// backend decides unless `@repr("C")` fixes it (LR73).
    pub fields: Vec<Field>,
    /// Whether the type has reference semantics (LR29, LR31).
    pub reference: bool,
}

/// One variant of an enum (LR15.2).
#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    pub name: String,
    /// What the variant carries. A tuple payload names its fields by
    /// position, so those names are `0`, `1`, and so on.
    pub fields: Vec<Field>,
}

/// An enum (LR15). A variant's index in `variants` is its tag.
#[derive(Debug, Clone, PartialEq)]
pub struct Enum {
    pub variants: Vec<Variant>,
}

/// One method an interface requires (LR18).
#[derive(Debug, Clone, PartialEq)]
pub struct Method {
    pub name: String,
    pub params: Vec<Ty>,
    pub result: Ty,
}

/// One type's implementation of an interface: its method table (LR18.1).
#[derive(Debug, Clone, PartialEq)]
pub struct Implementation {
    pub ty: TypeId,
    /// The function each of the interface's method slots resolves to, in slot
    /// order. This is the vtable a `CallVirtual` reads at runtime, and what
    /// devirtualization reads at compile time.
    pub methods: Vec<FuncId>,
}

/// An interface (LR18). A method's index in `methods` is the slot a
/// `CallVirtual` names.
#[derive(Debug, Clone, PartialEq)]
pub struct Interface {
    pub methods: Vec<Method>,
    /// Every type that implements it, which is what devirtualization counts
    /// (LR18.1).
    pub implementors: Vec<Implementation>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Shape {
    Struct(Struct),
    Enum(Enum),
    Interface(Interface),
}

/// A declared type: what it is called, what it takes, and what it holds.
#[derive(Debug, Clone, PartialEq)]
pub struct Nominal {
    /// How the type is written in the program, for diagnostics and for the
    /// names monomorphization gives its instances.
    pub name: String,
    /// Its type parameters, in declaration order (LR19). Empty once
    /// monomorphization has substituted them.
    pub type_params: Vec<String>,
    pub shape: Shape,
    pub span: Span,
}

/// A run of instructions with one entry and one exit.
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    /// The values this block receives from whoever jumped to it. These take
    /// the place of phi nodes: a value that differs between paths becomes a
    /// parameter, and each jump passes what it holds.
    pub params: Vec<Value>,
    pub insts: Vec<Inst>,
    /// Absent only while the block is being built. A finished function has
    /// one on every block.
    pub term: Option<Terminator>,
}

impl Block {
    #[must_use]
    fn new() -> Self {
        Self {
            params: Vec::new(),
            insts: Vec::new(),
            term: None,
        }
    }
}

/// One function, in SSA.
#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    /// A name unique in the program: the module it came from and the path to
    /// it inside that module.
    pub name: String,
    /// Its type parameters, in declaration order (LR19). Empty once
    /// monomorphization has substituted them.
    pub type_params: Vec<String>,
    /// The types of the entry block's parameters, in order. A method takes
    /// `self` as the first of them (LR65).
    pub params: Vec<Ty>,
    /// What `Return` gives back. [`Ty::Unit`] where the function writes no
    /// result (LR9.1).
    pub result: Ty,
    /// Whether calling it produces a `Task<T>` rather than running it (LR27).
    /// The pass that turns one into a state machine reads this.
    pub asynchronous: bool,
    /// Where it was written, for diagnostics and backtraces.
    pub span: Span,
    /// The block control enters at. Its parameters are the function's.
    pub entry: BlockId,
    blocks: Vec<Block>,
    /// The type of every value, indexed by [`Value`].
    values: Vec<Ty>,
    slots: Vec<Ty>,
}

impl Function {
    /// A function with one empty entry block, whose parameters are `params`.
    #[must_use]
    pub fn new(name: String, params: Vec<Ty>, result: Ty, span: Span) -> Self {
        let mut function = Self {
            name,
            type_params: Vec::new(),
            params: params.clone(),
            result,
            asynchronous: false,
            span,
            entry: BlockId(0),
            blocks: vec![Block::new()],
            values: Vec::new(),
            slots: Vec::new(),
        };
        for ty in params {
            let value = function.add_value(ty);
            function.blocks[0].params.push(value);
        }
        function
    }

    /// Introduces a value of type `ty`. The instruction or block parameter
    /// that produces it is what makes it defined; this only reserves it.
    pub fn add_value(&mut self, ty: Ty) -> Value {
        let value = Value(u32::try_from(self.values.len()).expect("value count fits in u32"));
        self.values.push(ty);
        value
    }

    /// # Panics
    #[must_use]
    pub fn type_of(&self, value: Value) -> &Ty {
        self.values
            .get(value.0 as usize)
            .expect("value belongs to another function")
    }

    /// Adds an empty block with no parameters.
    pub fn add_block(&mut self) -> BlockId {
        let id = BlockId(u32::try_from(self.blocks.len()).expect("block count fits in u32"));
        self.blocks.push(Block::new());
        id
    }

    /// Adds a parameter of type `ty` to `block`, and returns the value the
    /// block receives.
    ///
    /// # Panics
    pub fn add_block_param(&mut self, block: BlockId, ty: Ty) -> Value {
        let value = self.add_value(ty);
        self.block_mut(block).params.push(value);
        value
    }

    /// Adds a stack slot holding a `ty` (LR72).
    pub fn add_slot(&mut self, ty: Ty) -> SlotId {
        let id = SlotId(u32::try_from(self.slots.len()).expect("slot count fits in u32"));
        self.slots.push(ty);
        id
    }

    /// # Panics
    #[must_use]
    pub fn slot_type(&self, slot: SlotId) -> &Ty {
        self.slots
            .get(slot.0 as usize)
            .expect("slot belongs to another function")
    }

    /// # Panics
    #[must_use]
    pub fn block(&self, block: BlockId) -> &Block {
        self.blocks
            .get(block.0 as usize)
            .expect("block belongs to another function")
    }

    /// # Panics
    pub fn block_mut(&mut self, block: BlockId) -> &mut Block {
        self.blocks
            .get_mut(block.0 as usize)
            .expect("block belongs to another function")
    }

    /// Every block, in the order they were added. The entry block is first.
    pub fn blocks(&self) -> impl Iterator<Item = (BlockId, &Block)> {
        self.blocks
            .iter()
            .enumerate()
            .map(|(i, block)| (BlockId(i as u32), block))
    }

    pub fn blocks_mut(&mut self) -> impl Iterator<Item = &mut Block> {
        self.blocks.iter_mut()
    }

    /// Whether the function is a template rather than code: something a call
    /// instantiates rather than jumps to (LR19).
    #[must_use]
    pub fn is_template(&self) -> bool {
        !self.type_params.is_empty()
    }

    /// Replaces `params` with `args` in the type of every value and slot.
    pub fn substitute_values(&mut self, params: &[String], args: &[Ty]) {
        for ty in self.values.iter_mut().chain(&mut self.slots) {
            *ty = ty.substitute(params, args);
        }
    }

    #[must_use]
    pub fn slots(&self) -> &[Ty] {
        &self.slots
    }
}

/// Every type and function one compilation reaches.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Program {
    types: Vec<Nominal>,
    functions: Vec<Function>,
    /// The function the program starts at (LR45). Absent for an artifact that
    /// is not an executable (LR77).
    pub entry: Option<FuncId>,
    /// Module initializers, in the order they must run before `main` (LR78).
    pub initializers: Vec<FuncId>,
    /// Where each type came from, so a pass can find one it did not build.
    by_name: BTreeMap<String, TypeId>,
}

impl Program {
    pub fn add_type(&mut self, nominal: Nominal) -> TypeId {
        let id = TypeId(u32::try_from(self.types.len()).expect("type count fits in u32"));
        self.by_name.insert(nominal.name.clone(), id);
        self.types.push(nominal);
        id
    }

    /// # Panics
    #[must_use]
    pub fn nominal(&self, id: TypeId) -> &Nominal {
        self.types
            .get(id.0 as usize)
            .expect("type belongs to another program")
    }

    /// # Panics
    pub fn nominal_mut(&mut self, id: TypeId) -> &mut Nominal {
        self.types
            .get_mut(id.0 as usize)
            .expect("type belongs to another program")
    }

    /// The type registered under `name`, if there is one.
    #[must_use]
    pub fn find_type(&self, name: &str) -> Option<TypeId> {
        self.by_name.get(name).copied()
    }

    pub fn add_function(&mut self, function: Function) -> FuncId {
        let id = FuncId(u32::try_from(self.functions.len()).expect("function count fits in u32"));
        self.functions.push(function);
        id
    }

    /// # Panics
    #[must_use]
    pub fn function(&self, id: FuncId) -> &Function {
        self.functions
            .get(id.0 as usize)
            .expect("function belongs to another program")
    }

    /// # Panics
    pub fn function_mut(&mut self, id: FuncId) -> &mut Function {
        self.functions
            .get_mut(id.0 as usize)
            .expect("function belongs to another program")
    }

    pub fn functions(&self) -> impl Iterator<Item = (FuncId, &Function)> {
        self.functions
            .iter()
            .enumerate()
            .map(|(i, function)| (FuncId(i as u32), function))
    }

    pub fn types(&self) -> impl Iterator<Item = (TypeId, &Nominal)> {
        self.types
            .iter()
            .enumerate()
            .map(|(i, nominal)| (TypeId(i as u32), nominal))
    }
}
