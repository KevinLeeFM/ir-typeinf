import Mathlib.Data.Quot

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

-- Equivalence and Setoid

inductive IRTypeEquiv : IRTypeSyntax → IRTypeSyntax → Prop where
  | refl (t : IRTypeSyntax) : IRTypeEquiv t t
  | symm {t1 t2 : IRTypeSyntax} : IRTypeEquiv t1 t2 → IRTypeEquiv t2 t1
  | trans {t1 t2 t3 : IRTypeSyntax} : IRTypeEquiv t1 t2 → IRTypeEquiv t2 t3 → IRTypeEquiv t1 t3
  | ptr_congr {t1 t2 : IRTypeSyntax} : IRTypeEquiv t1 t2 → IRTypeEquiv (.ptr t1) (.ptr t2)
  | seq_congr {t1 t2 : IRTypeSyntax} : IRTypeEquiv t1 t2 → IRTypeEquiv (.seq t1) (.seq t2)
  | prod_congr {t1 t2 t1' t2' : IRTypeSyntax} :
    IRTypeEquiv t1 t1' → IRTypeEquiv t2 t2' →
    IRTypeEquiv (.prod t1 t2) (.prod t1' t2')
  | sum_congr {t1 t2 t1' t2' : IRTypeSyntax} :
    IRTypeEquiv t1 t1' → IRTypeEquiv t2 t2' →
    IRTypeEquiv (.sum t1 t2) (.sum t1' t2')
  | sum_comm (t1 t2 : IRTypeSyntax) : IRTypeEquiv (.sum t1 t2) (.sum t2 t1)
  | sum_assoc (t1 t2 t3 : IRTypeSyntax) : IRTypeEquiv (.sum (.sum t1 t2) t3) (.sum t1 (.sum t2 t3))
  | prod_dist_l (t1 t2 t3 : IRTypeSyntax) :
    IRTypeEquiv (.prod t1 (.sum t2 t3)) (.sum (.prod t1 t2) (.prod t1 t3))
  | prod_dist_r (t1 t2 t3 : IRTypeSyntax) :
    IRTypeEquiv (.prod (.sum t1 t2) t3) (.sum (.prod t1 t3) (.prod t2 t3))
  | sum_bot (t : IRTypeSyntax) : IRTypeEquiv (.sum IRTypeSyntax.bot t) t
  | seq_absorb (t : IRTypeSyntax) : IRTypeEquiv (.prod t (.seq t)) (.seq t)

instance irTypeSetoid : Setoid IRTypeSyntax where
  r := IRTypeEquiv
  iseqv := by
    constructor
    · intro t; apply IRTypeEquiv.refl
    · intro t1 t2 h; apply IRTypeEquiv.symm; assumption
    · intro t1 t2 t3 h1 h2; apply IRTypeEquiv.trans h1 h2

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
    apply IRTypeEquiv.ptr_congr
    assumption
  ) t

def seq (t : IRType) : IRType :=
  Quot.lift (fun t' ↦ mk (IRTypeSyntax.seq t')) (by
    intro t1 t2 h
    apply Quot.sound
    apply IRTypeEquiv.seq_congr
    assumption
  ) t

def prod (t1 t2 : IRType) : IRType :=
  Quot.lift₂ (fun t1' t2' ↦ mk (IRTypeSyntax.prod t1' t2')) (by
    intro t1a t1b h1 t2a
    apply Quot.sound
    apply IRTypeEquiv.prod_congr
    · apply IRTypeEquiv.refl
    · assumption
  ) (by
    intro t2a t2b h2 t1a
    apply Quot.sound
    apply IRTypeEquiv.prod_congr
    · assumption
    · apply IRTypeEquiv.refl
  ) t1 t2

def sum (t1 t2 : IRType) : IRType :=
  Quot.lift₂ (fun t1' t2' ↦ mk (IRTypeSyntax.sum t1' t2')) (by
    intro t1a t1b h1 t2a
    apply Quot.sound
    apply IRTypeEquiv.sum_congr
    · apply IRTypeEquiv.refl
    · assumption
  ) (by
    intro t2a t2b h2 t1a
    apply Quot.sound
    apply IRTypeEquiv.sum_congr
    · assumption
    · apply IRTypeEquiv.refl
  ) t1 t2

-- Subtyping relation

inductive Le : IRType → IRType → Prop where
  | refl (t : IRType) : Le t t
  | trans {t1 t2 t3 : IRType} : Le t1 t2 → Le t2 t3 → Le t1 t3
  | bot_le (t : IRType) : Le bot t
  | le_top (t : IRType) : Le t top
  | prod (t1 t2 t1' t2') : Le t1 t1' → Le t2 t2' → Le (prod t1 t2) (prod t1' t2')
  | sum (t1 t2 t1' t2') : Le t1 t1' → Le t2 t2' → Le (sum t1 t2) (sum t1' t2')
  | ptr (t t') : Le t t' → Le (ptr t) (ptr t')
  | seq_intro (t) : Le t (seq t)
  | seq_prod (t1 t2) : Le t1 (seq t2) → Le (prod t2 t1) (seq t2)

end IrTypeinf
