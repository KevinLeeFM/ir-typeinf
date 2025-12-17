import IrTypeinf.Type

namespace IrTypeinf

-- Variable names
abbrev Var := Nat
abbrev Addr := Nat

structure Ptr where
  addr : Addr
  offset : Nat
deriving Repr, DecidableEq

abbrev Val := List (Int ⊕ Ptr)

structure State where
  assign : Var → Val
  mem : Addr → Option Val

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

-- 0 truncates everything
def truncValRight : Nat → Val → Val -- FIXME
  | 0, _ => []
  | .succ i, v =>
    match v with
    | [] => []
    | e :: vs => e :: truncValRight i vs

#eval truncValRight 2 [Sum.inl 1, Sum.inl 2, Sum.inl 3]

def truncValLeft : Nat → Val → Val -- FIXME
  | 0, v => v
  | .succ i, v =>
    match v with
    | [] => []
    | _ :: vs => truncValLeft i vs

#eval truncValLeft 2 [Sum.inl 1, Sum.inl 2, Sum.inl 3]

def TypeDecl := Var → Option IRType

def Prog := TypeDecl × Set Stmt × TypeDecl

def isInt (v : Val) : Prop :=
  ∃ n : Int, v = [Sum.inl n]

def pointsTo (σ : State) (vp v : Val) : Prop :=
  match v with
  | [Sum.inr p] =>
      match (σ.mem p.addr) with
      | some v' => .extract v' (start := p.offset) = vp
      | none => False
  | _ => False

inductive TypeConcret : State → Val → IRType → Prop where
  | top (σ : State) (v : Val) :
    TypeConcret σ v top

  | empty (σ : State) (τ : IRType) :
    TypeConcret σ [] τ

  | int (σ : State) (v : Val) :
    isInt v →
    TypeConcret σ v int

  | ptr (σ : State) (v_p v : Val) (τ : IRType) :
    TypeConcret σ v τ →
    pointsTo σ v_p v →
    TypeConcret σ v_p (ptr τ)

  | prod (σ : State) (v₁ v₂ v : Val) (τ₁ τ₂ : IRType) :
    TypeConcret σ v₁ τ₁ →
    TypeConcret σ v₂ τ₂ →
    v = v₁ ++ v₂ →
    TypeConcret σ v (prod τ₁ τ₂)

  | sum_left (σ : State) (v : Val) (τ₁ τ₂ : IRType) :
    TypeConcret σ v τ₁ →
    TypeConcret σ v (sum τ₁ τ₂)

  | sum_right (σ : State) (v : Val) (τ₁ τ₂ : IRType) :
    TypeConcret σ v τ₂ →
    TypeConcret σ v (sum τ₁ τ₂)

  | seq (σ : State) (v_h v_t v : Val) (τ : IRType) :
    TypeConcret σ v_h τ →
    TypeConcret σ v_t (seq τ) →
    v = v_h ++ v_t →
    TypeConcret σ v (seq τ)

def typeDeref : IRTypeSyntax → IRTypeSyntax :=
  fun τ ↦ match τ with
    | .ptr τ' => τ'
    | _ => .bot

def freshAddr (σ : State) (a : Addr) : Prop :=
  σ.mem a = none

def writeAssign (σ : State) (v : Val) (x : Var) : State :=
  { assign := fun y ↦ if y = x then v else σ.assign y,
    mem := σ.mem }

def valPatch (l1 l2 : Val) (offset : Nat) :=
  let (left, rest) := l1.splitAt offset
  left ++ l2 ++ rest.drop l2.length

#eval valPatch [Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4] [Sum.inl 9, Sum.inl 8] 1
#eval valPatch [Sum.inl 1, Sum.inl 2] [Sum.inl 9, Sum.inl 8] 1

def initMem (σ : State) (v : Val) (addr : Addr) : State :=
  { assign := σ.assign,
    mem := fun b ↦ if b = addr then some v else σ.mem b }

def writeMem (σ : State) (v : Val) (p : Ptr) (validP : TypeConcret ) : State :=
  { assign := σ.assign,
    mem := fun b ↦ if b = p.addr then (
      match σ.mem b with
      | some old_val => some (valPatch old_val v p.offset)
      | none =>
    ) else σ.mem b }

inductive StmtReach : Stmt → State → State → Prop where
  | alloca (v : Var) (τ : IRTypeSyntax) (σ σ' : State) (a : Addr) (ndv : Val) :
    freshAddr σ a →
    TypeConcret σ ndv (mk (typeDeref τ)) →
    -- Initialize with a non-deterministic value
    σ' = writeAssign (initMem σ ndv a) [Sum.inr { addr := a, offset := 0 }] v →
    StmtReach (Stmt.alloca v τ) σ σ'

  -- FIXME
  | store {p} (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax)
      (σ σ' : State) (val val' : Val)  :
    σ.assign v₂ = [Sum.inr p] →
    σ.assign v₁ = val →
    val' = truncValRight p.offset val →
    σ' = writeMem σ val' p.addr →
    StmtReach (Stmt.store v₁ τ₁ v₂ τ₂) σ σ'

  -- FIXME
  | load {p} (v₁ : Var) (τ₁ : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax)
      (σ σ' : State) (val val' : Val) :
    σ.assign v₂ = [Sum.inr p] →
    σ.mem p.addr = some val →
    val' = truncValRight p.offset val →
    σ' = writeAssign σ val' v₁ →
    StmtReach (Stmt.load v₁ τ₁ v₂ τ₂) σ σ'

  -- FIXME
  | gep {p} (v₁ : Var) (τs : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax)
      (i : Nat) (σ σ' : State) (val val' : Val) :
    σ.assign v₂ = [Sum.inr p] →
    σ.mem p.addr = some val →
    val' = truncValRight i val →
    σ' = writeAssign σ val' v₁ →
    StmtReach (Stmt.gep v₁ τs v₂ τ₂ i) σ σ'

  -- FIXME
  | gepv {p} (v₁ : Var) (τs : IRTypeSyntax) (v₂ : Var) (τ₂ : IRTypeSyntax)
      (vi : Var) (σ σ' : State) (a : Addr) (i : Int) (val val' : Val) :
    σ.assign v₂ = [Sum.inr p] →
    σ.assign vi = [Sum.inl i] →
    σ.mem p.addr = some val →
    i ≥ 0 →
    val' = truncValRight (Nat.ofInt i) val →
    σ' = writeAssign σ val' v₁ →
    StmtReach (Stmt.gepv v₁ τs v₂ τ₂ vi) σ σ'

end IrTypeinf
