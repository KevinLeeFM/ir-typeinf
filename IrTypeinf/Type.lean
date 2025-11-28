import Mathlib.Data.Quot
import Mathlib.Order.Defs.PartialOrder

import Aesop

namespace IrTypeinf

inductive IRTypeSyntax where
  | bot : IRTypeSyntax
  | top : IRTypeSyntax
  | int : IRTypeSyntax
  | ptr : IRTypeSyntax → IRTypeSyntax
  | seq : IRTypeSyntax → IRTypeSyntax
  | prod : IRTypeSyntax → IRTypeSyntax → IRTypeSyntax
  | sum : IRTypeSyntax → IRTypeSyntax → IRTypeSyntax
deriving Repr, DecidableEq

@[aesop safe [constructors, cases, apply]]
inductive LeSyntax : IRTypeSyntax → IRTypeSyntax → Prop where
  | refl (t : IRTypeSyntax) : LeSyntax t t
  | trans {t₁ t₂ t₃ : IRTypeSyntax} :
      LeSyntax t₁ t₂ → LeSyntax t₂ t₃ → LeSyntax t₁ t₃

  -- lattice-ish structure
  | bot_le (t : IRTypeSyntax) : LeSyntax .bot t
  | le_top (t : IRTypeSyntax) : LeSyntax t .top

  -- monotone constructors
  | ptr {t t'} :
      LeSyntax t t' → LeSyntax (.ptr t) (.ptr t')
  | seq {t t'} :
      LeSyntax t t' → LeSyntax (.seq t) (.seq t')

  | prod {t₁ t₂ t₁' t₂'} :
      LeSyntax t₁ t₁' → LeSyntax t₂ t₂' →
      LeSyntax (.prod t₁ t₂) (.prod t₁' t₂')

  | sum {t₁ t₂ t₁' t₂'} :
      LeSyntax t₁ t₁' → LeSyntax t₂ t₂' →
      LeSyntax (.sum t₁ t₂) (.sum t₁' t₂')

  -- algebraic laws for sum: commutativity + associativity (both directions)
  | sum_comm_l (t₁ t₂ : IRTypeSyntax) :
      LeSyntax (.sum t₁ t₂) (.sum t₂ t₁)
  | sum_comm_r (t₁ t₂ : IRTypeSyntax) :
      LeSyntax (.sum t₂ t₁) (.sum t₁ t₂)

  | sum_assoc_l (t₁ t₂ t₃ : IRTypeSyntax) :
      LeSyntax (.sum (.sum t₁ t₂) t₃) (.sum t₁ (.sum t₂ t₃))
  | sum_assoc_r (t₁ t₂ t₃ : IRTypeSyntax) :
      LeSyntax (.sum t₁ (.sum t₂ t₃)) (.sum (.sum t₁ t₂) t₃)

  -- distributivity of product over sum, both directions
  | prod_dist_l₁ (t₁ t₂ t₃ : IRTypeSyntax) :
      LeSyntax (.prod t₁ (.sum t₂ t₃)) (.sum (.prod t₁ t₂) (.prod t₁ t₃))
  | prod_dist_l₂ (t₁ t₂ t₃ : IRTypeSyntax) :
      LeSyntax (.sum (.prod t₁ t₂) (.prod t₁ t₃)) (.prod t₁ (.sum t₂ t₃))

  | prod_dist_r₁ (t₁ t₂ t₃ : IRTypeSyntax) :
      LeSyntax (.prod (.sum t₁ t₂) t₃) (.sum (.prod t₁ t₃) (.prod t₂ t₃))
  | prod_dist_r₂ (t₁ t₂ t₃ : IRTypeSyntax) :
      LeSyntax (.sum (.prod t₁ t₃) (.prod t₂ t₃)) (.prod (.sum t₁ t₂) t₃)

  -- sum with bot
  | sum_bot_l (t : IRTypeSyntax) :
      LeSyntax (.sum .bot t) t
  | sum_bot_r (t : IRTypeSyntax) :
      LeSyntax t (.sum .bot t)

  -- seq absorption: t × seq t ≈ seq t
  | seq_absorb_l (t : IRTypeSyntax) :
      LeSyntax (.prod t (.seq t)) (.seq t)
  | seq_absorb_r (t : IRTypeSyntax) :
      LeSyntax (.seq t) (.prod t (.seq t))

  -- "typing-ish" rules:
  | seq_intro (t : IRTypeSyntax) :
      LeSyntax t (.seq t)

  | seq_prod (t₁ t₂ : IRTypeSyntax) :
      LeSyntax t₁ (.seq t₂) →
      LeSyntax (.prod t₂ t₁) (.seq t₂)

infix:50 " ≤ₛ " => LeSyntax

def IRTypeEquiv : IRTypeSyntax → IRTypeSyntax → Prop :=
  fun t1 t2 ↦ t1 ≤ₛ t2 ∧ t2 ≤ₛ t1

def IRTypeEquiv_iseqv : Equivalence IRTypeEquiv where
  refl := by
    intro t
    constructor
    · apply LeSyntax.refl
    · apply LeSyntax.refl
  symm := by
    intro x y h
    constructor
    · exact h.right
    · exact h.left
  trans := by
    intro x y z h1 h2
    constructor
    · apply LeSyntax.trans h1.left h2.left
    · apply LeSyntax.trans h2.right h1.right

def irTypeSetoid : Setoid IRTypeSyntax where
  r := IRTypeEquiv
  iseqv := IRTypeEquiv_iseqv

def IRType := Quotient irTypeSetoid

-- Map from syntax to type

def mk : IRTypeSyntax → IRType :=
  Quot.mk _

def bot : IRType := mk IRTypeSyntax.bot
def top : IRType := mk IRTypeSyntax.top
def int : IRType := mk IRTypeSyntax.int

def ptr (t : IRType) : IRType :=
  Quot.lift (fun t' ↦ mk (IRTypeSyntax.ptr t')) (by
    intro t1 t2 h
    apply Quot.sound
    cases h
    constructor <;> apply LeSyntax.ptr <;> assumption
  ) t

def seq (t : IRType) : IRType :=
  Quot.lift (fun t' ↦ mk (IRTypeSyntax.seq t')) (by
    intro t1 t2 h
    apply Quot.sound
    cases h
    constructor <;> apply LeSyntax.seq <;> assumption
  ) t

def prod (t1 t2 : IRType) : IRType :=
  Quot.lift₂ (fun t1' t2' ↦ mk (IRTypeSyntax.prod t1' t2')) (by
    intro t1a t1b h1 t2a
    apply Quot.sound
    cases t2a
    constructor <;> apply LeSyntax.prod <;> first | apply LeSyntax.refl | assumption
  ) (by
    intro t2a t2b h2 t1a
    apply Quot.sound
    cases t1a
    constructor <;> apply LeSyntax.prod <;> first | apply LeSyntax.refl | assumption
  ) t1 t2

def sum (t1 t2 : IRType) : IRType :=
  Quot.lift₂ (fun t1' t2' ↦ mk (IRTypeSyntax.sum t1' t2')) (by
    intro t1a t1b h1 t2a
    apply Quot.sound
    cases t2a
    constructor <;> apply LeSyntax.sum <;> first | apply LeSyntax.refl | assumption
  ) (by
    intro t2a t2b h2 t1a
    apply Quot.sound
    cases t1a
    constructor <;> apply LeSyntax.sum <;> first | apply LeSyntax.refl | assumption
  ) t1 t2

def Le (t1 t2 : IRType) : Prop :=
  Quot.lift₂ (fun t1' t2' ↦ LeSyntax t1' t2') (by
    intro t1a t1b h1 t2a
    simp
    cases t2a
    constructor <;> intro <;> apply LeSyntax.trans <;> assumption
  ) (by
    intro t2a t2b h2 t1a
    simp
    cases t1a
    constructor <;> intro <;> apply LeSyntax.trans <;> assumption
  ) t1 t2

infix:50 " ≤ " => Le

def Lt (t1 t2 : IRType) : Prop :=
  t1 ≤ t2 ∧ ¬ (t2 ≤ t1)

infix:50 " < " => Lt

def LeSyntax_imply_Le {t1 t2 : IRTypeSyntax} :
    t1 ≤ₛ t2 → (mk t1) ≤ (mk t2) := by
  intro h
  change LeSyntax t1 t2
  assumption

def Le_imply_LeSyntax {t1 t2 : IRTypeSyntax} :
    (mk t1) ≤ (mk t2) → t1 ≤ₛ t2 := by
  intro h
  change LeSyntax t1 t2 at h
  assumption

-- We now prove some basic properties to assure that Le is a partial order

instance : PartialOrder IRType where
  le := Le
  lt := Lt

  le_refl := by
    intro t
    apply Quot.ind (β := fun t' ↦ t' ≤ t') (by
      intro t'
      apply LeSyntax_imply_Le
      apply LeSyntax.refl) t

  le_trans := by
    intro a b c hab hbc
    apply Quot.induction_on₃ (δ := fun a b c ↦ a ≤ b → b ≤ c → a ≤ c) a b c (by
      intro ta tb tc hab' hbc'
      apply LeSyntax_imply_Le
      have habs := Le_imply_LeSyntax hab'
      have hbcs := Le_imply_LeSyntax hbc'
      apply LeSyntax.trans habs hbcs
    ) (by exact hab) (by exact hbc)

  le_antisymm := by
    intro a b hab hba
    apply Quot.induction_on₂ (δ := fun a b ↦ a ≤ b → b ≤ a → a = b) a b (by
      intro ta tb hab' hba'
      have habs := Le_imply_LeSyntax hab'
      have hbas := Le_imply_LeSyntax hba'
      apply Quot.sound
      constructor <;> assumption
    ) (by exact hab) (by exact hba)

end IrTypeinf
