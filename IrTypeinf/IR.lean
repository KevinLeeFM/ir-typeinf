import IrTypeinf.Type

namespace IrTypeinf

-- Variable names
abbrev Var := Nat
abbrev Addr := Nat

structure Ptr where
  addr : Addr
  offset : Nat
deriving Repr, DecidableEq

inductive Cell where
  | int (n : Int)
  | ptr (p : Ptr)
deriving Repr, DecidableEq

abbrev Val := Option (List Cell)

structure State where
  stack : Var → Val
  mem : Addr → Val

-- Statement inductive type based on the given grammar
inductive Stmt where
  -- v := mono("alloca")(τ)
  | alloca (v : Var) (τ : IRTypeSyntax) : Stmt

  -- mono("store")(v_1 : τ_1, v_2 : τ_2)
  | store (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax) : Stmt

  -- v_1 := mono("load")_τ_1 (v_2 : τ_2)
  | load (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax) : Stmt

  -- v_1 := mono("gep")(τ_s, v_2 : τ_2, i)
  | gep (v₁ : Var) (τ_s : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax) (i : Nat) : Stmt

  -- v_1 := mono("gepv")(τ_s, v_2 : τ_2, vi)
  | gepv (v₁ : Var) (τ_s : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax) (vi : Var) : Stmt

  -- v_1 := mono("bitcast")_τ_1 (v_2 : τ_2)
  | bitcast (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax) : Stmt

  -- v_1 := mono("phi")_τ_1 (v_2, v_3)
  | phi (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (v₃ : Var) : Stmt

  -- v_r := star_τ_r (x_1 : τ_1, ..., x_n : τ_n)
  | star (v_r : Var) (τ_r : IRTypeSyntax) (args : List (Var × IRTypeSyntax)) : Stmt

  -- v_1, v_2 := mono("fork")(v)
  | fork (v₁ : Var) (v₂ : Var) (v : Var) : Stmt
deriving Repr

-- Truncation function
-- NOTE: only works when IRTypeSyntax is in a specific normal form.
-- TODO: May want to run normalization first.
-- Product must be (a × (b × (...)))
def truncType : Nat → IRTypeSyntax → IRTypeSyntax
  | 0, σ => σ
  | .succ i, σ =>
    match σ with
    | .top => .top
    | .bot => .bot
    | .seq α => .seq α
    | .prod _σ₁ σ₂ => truncType i σ₂
    | .sum (.prod σ₁ σ₂) (.prod ρ₁ ρ₂) =>
      .sum (truncType (.succ i) (.prod σ₁ σ₂)) (truncType (.succ i) (.prod ρ₁ ρ₂))
    | _ => .bot

def TypeDecl := Var → Option IRType

def Prog := TypeDecl × Set Stmt × TypeDecl

def isInt (v : Val) : Prop :=
  ∃ n : Int, v = some [Cell.int n]

-- Whether v_p points to the value v in the memory state σ
def pointsTo (σ : State) (vp v : Val) : Prop :=
  match v with
  | some [Cell.ptr p] =>
      match σ.mem p.addr with
      | some v' => some (.extract v' (start := p.offset)) = vp
      | none => False
  | _ => False

-- NOTE: This only validates if v is a value of such type that is not followed by any other fields
-- TODO: depending on the formulation of the remaining file, this may be too strict
inductive TypeConcret : State → Val → IRType → Prop where
  -- Every value belongs to top type
  | top (σ : State) (v : Val) :
    TypeConcret σ v top

  -- None value belongs to every type, including bottom (uninitialized memory)
  | none (σ : State) (τ : IRType) :
    TypeConcret σ none τ

  | int (σ : State) (v : Val) :
    isInt v →
    TypeConcret σ v int

  | ptr (σ : State) (v_p v : Val) (τ : IRType) :
    TypeConcret σ v τ →
    pointsTo σ v_p v →
    TypeConcret σ v_p (ptr τ)

  | prod (σ : State) (l₁ l₂ : List Cell) (τ₁ τ₂ : IRType) :
    TypeConcret σ (some l₁) τ₁ →
    TypeConcret σ (some l₂) τ₂ →
    TypeConcret σ (some (l₁ ++ l₂)) (prod τ₁ τ₂)

  | sum_left (σ : State) (v : Val) (τ₁ τ₂ : IRType) :
    TypeConcret σ v τ₁ →
    TypeConcret σ v (sum τ₁ τ₂)

  | sum_right (σ : State) (v : Val) (τ₁ τ₂ : IRType) :
    TypeConcret σ v τ₂ →
    TypeConcret σ v (sum τ₁ τ₂)

  | seq_intro (σ : State) (l : List Cell) (τ : IRType) :
    TypeConcret σ (some l) τ →
    TypeConcret σ (some l) (seq τ)

  | seq_prod (σ : State) (l_h l_t : List Cell) (τ : IRType) :
    TypeConcret σ (some l_h) τ →
    TypeConcret σ (some l_t) (seq τ) →
    TypeConcret σ (some (l_h ++ l_t)) (seq τ)

def typeDeref : IRTypeSyntax → IRTypeSyntax :=
  fun τ ↦ match τ with
    | .ptr τ' => τ'
    | _ => .bot

def freshAddr (σ : State) (a : Addr) : Prop :=
  σ.mem a = none

def writeAssign (σ : State) (v : Val) (x : Var) : State :=
  { stack := fun y ↦ if y = x then v else σ.stack y,
    mem := σ.mem }

def valPatch (l1 l2 : Val) (offset : Nat) : Val :=
  match l1, l2 with
  | some l1', some l2' =>
      let (left, rest) := l1'.splitAt offset
      some (left ++ l2' ++ rest.drop l2'.length)
  | _, _ => l1

#eval valPatch
  (some [Cell.int 1, Cell.int 2, Cell.int 3, Cell.int 4])
  (some [Cell.int 9, Cell.int 8]) 1
#eval valPatch (some [Cell.int 1, Cell.int 2]) (some [Cell.int 9, Cell.int 8]) 1

def truncValLeft (offset : Nat) (v : Val) : Val :=
  match v with
  | some l => some (l.take offset)
  | none => none

def truncValRight (offset : Nat) (v : Val) : Val :=
  match v with
  | some l => some (l.drop offset)
  | none => none

-- Initializes memory at address addr to none
def initMem (σ : State) (addr : Addr) : State :=
  { stack := σ.stack,
    mem := fun b ↦ if b = addr then none else σ.mem b }

def writeMem (σ : State) (v : Val) (p : Ptr) : State :=
  { stack := σ.stack,
    mem := fun b ↦ if b = p.addr then valPatch (σ.mem b) v p.offset else σ.mem b }

-- Small-step, flow-insensitive operational semantics for statements
-- "Runtime" type check is enforced. Ill-typed statements will get "stuck" and will not execute
-- While variables are overwrittable, they must only be used for the same type throughout the
-- program.
-- A value on the stack is only well-typed if it is not followed by any other fields.
--   - For instance a struct starting with an int cannot be used as an int.
-- However, a value on the memory can be well-typed even if it is followed by other fields.
--  - Note that the program still needs to state it as Ptr(τ × ...)
inductive StmtReach : Stmt → State → State → Prop where
  | alloca (v : Var) (τ : IRTypeSyntax) (σ σ' : State) (a : Addr) :
    freshAddr σ a →
    -- Initialize with an uninitialized memory cell
    σ' = writeAssign (initMem σ a) (some [Cell.ptr { addr := a, offset := 0 }]) v →
    StmtReach (Stmt.alloca v τ) σ σ'

  | store {p val₁ val₂'} (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax)
      (σ σ' : State) :
    σ.stack v₂ = some [Cell.ptr p] →
    σ.stack v₁ = val₁ →

    -- "Run-time" type checks
    TypeConcret σ (σ.stack v₁) (mk τ₁) →
    TypeConcret σ (σ.stack v₂) (mk τ₂) →
    (mk τ₂) = ptr (mk τ₁) →

    -- We are assured that patching will not pollute other memory cells since type checks passed
    val₂' = valPatch (σ.mem p.addr) (σ.stack v₁) p.offset →
    σ' = writeMem σ val₂' p →
    StmtReach (Stmt.store v₁ τ₁ v₂ τ₂) σ σ'

  | load {p val₂ val₁'} (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax) (i : Nat)
      (σ σ' : State) :
    σ.stack v₂ = some [Cell.ptr p] →
    σ.mem p.addr = val₂ →

    -- "Run-time" type checks
    TypeConcret σ (σ.stack v₂) (mk τ₂) →
    -- val₂ need not be type checked since we only load a segment val₁' of it.
    -- The segment val₁' is checked, however.
    TypeConcret σ val₁' (mk τ₁) →
    (mk τ₂) = ptr (mk τ₁) →

    -- The truncValLeft is performed at a non-deterministic offset i that only needs to
    -- respects the fact that val₁' after truncation is well-typed against τ₁.
    val₁' = (truncValLeft i (truncValRight p.offset val₂)) →
    σ' = writeAssign σ val₁' v₁ →
    StmtReach (Stmt.load v₁ τ₁ v₂ τ₂) σ σ'

  | gep {p₂ p₁' τ₁} (v₁ : Var) (τs : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax)
      (i : Nat) (σ σ' : State) (vals : Val) :
    σ.stack v₂ = some [Cell.ptr p₂] →
    σ.mem p₂.addr = vals →

    -- "Run-time" type checks
    TypeConcret σ (σ.stack v₂) (mk τ₂) →
    TypeConcret σ vals (mk τs) →
    TypeConcret σ (some [Cell.ptr p₁']) (mk τ₁) →
    (mk τ₁) = ptr (mk (truncType i τs)) →
    (mk τ₂) = ptr (mk τs) →

    p₁' = { addr := p₂.addr, offset := p₂.offset + i } →
    σ' = writeAssign σ (some [Cell.ptr p₁']) v₁ →
    StmtReach (Stmt.gep v₁ τs v₂ τ₂ i) σ σ'

  | gepv {p₂ p₁' τ₁ vals} (v₁ : Var) (τs : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax)
      (vi : Var) (σ σ' : State) (i : Int) :
    σ.stack v₂ = some [Cell.ptr p₂] →
    σ.stack vi = some [Cell.int i] →
    σ.mem p₂.addr = vals →

    -- Index assured to be non-negative so .toNat is safe
    0 ≤ i →

    -- "Run-time" type checks
    TypeConcret σ (σ.stack v₂) (mk τ₂) →
    TypeConcret σ vals (mk τs) →
    TypeConcret σ (some [Cell.ptr p₁']) (mk τ₁) →
    (mk τ₁) = ptr (mk (truncType i.toNat τs)) →
    (mk τ₂) = ptr (mk τs) →

    p₁' = { addr := p₂.addr, offset := p₂.offset + i.toNat } →
    σ' = writeAssign σ (some [Cell.ptr p₁']) v₁ →
    StmtReach (Stmt.gepv v₁ τs v₂ τ₂ vi) σ σ'

  | bitcast {val} (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax)
      (σ σ' : State) :
    val = σ.stack v₂ →

    -- "Run-time" type checks
    TypeConcret σ val (mk τ₁) →
    TypeConcret σ val (mk τ₂) →

    σ' = writeAssign σ val v₁ →
    StmtReach (Stmt.bitcast v₁ τ₁ v₂ τ₂) σ σ'

  | star {vals valsᵣ'} (v_r : Var) (τ_r : IRTypeSyntax) (args : List (Var × IRTypeSyntax))
      (σ σ' : State) :
    vals = args.map (fun (v, _) ↦ σ.stack v) →

    -- "Run-time" type checks
    (∀ v τ, (v, τ) ∈ args → TypeConcret σ (σ.stack v) (mk τ)) →
    -- Operator non-deterministically produces a value of the required type
    TypeConcret σ valsᵣ' (mk τ_r) →

    σ' = writeAssign σ (valsᵣ') v_r →
    StmtReach (Stmt.star v_r τ_r args) σ σ'

  | phi {val₂ val₃} (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (v₃ : Var)
      (σ σ' : State) :
    val₂ = σ.stack v₂ →
    val₃ = σ.stack v₃ →

    -- "Run-time" type checks
    TypeConcret σ val₂ (mk τ₁) →
    TypeConcret σ val₃ (mk τ₁) →

    -- Non-deterministic choice between val₂ and val₃
    (σ' = writeAssign σ val₂ v₁ ∨ σ' = writeAssign σ val₃ v₁) →
    StmtReach (Stmt.phi v₁ τ₁ v₂ v₃) σ σ'

  | fork {val} (v₁ : Var) (v₂ : Var) (v : Var)
      (σ σ' : State) :
    val = σ.stack v →

    -- Non-deterministic split of val into two parts
    σ' = writeAssign (writeAssign σ val v₁) val v₂ →
    StmtReach (Stmt.fork v₁ v₂ v) σ σ'

inductive SetStmtReach : Set Stmt → State → State → Prop where
  | step (s : Stmt) (S : Set Stmt) (σ σ' : State) :
    s ∈ S →
    StmtReach s σ σ' →
    SetStmtReach S σ σ'
  | trans (S : Set Stmt) (σ σ₁ σ₂ : State) :
    SetStmtReach S σ σ₁ →
    SetStmtReach S σ₁ σ₂ →
    SetStmtReach S σ σ₂

def TypeDeclInit (σ : State) (TD : TypeDecl) : Prop :=
  ∀ v, match TD v with
    | some τ => TypeConcret σ (σ.stack v) τ
    | none => TypeConcret σ (σ.stack v) bot

def TypeDeclAssert (σ : State) (TD : TypeDecl) : Prop :=
  ∀ v, match TD v with
    | some τ => TypeConcret σ (σ.stack v) τ
    | none => True

inductive ProgReach : Prog → State → Prop where
  | prog_reach {TD₁ S TD₂} (P : Prog) (σ₁ σ₂ : State) :
    P = (TD₁, S, TD₂) →
    TypeDeclInit σ₁ TD₁ →
    SetStmtReach S σ₁ σ₂ →
    TypeDeclAssert σ₂ TD₂ →
    ProgReach (TD₁, S, TD₂) σ₂

def TypeSoundness (P : Prog) (judge : Var → IRType) : Prop :=
  ∀ σ, ProgReach P σ →
  ∀ v,
    TypeConcret σ (σ.stack v) (judge v)

end IrTypeinf
