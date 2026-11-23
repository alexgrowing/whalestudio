import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory

noncomputable section

namespace PI.TripleFrameDeterminant

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section RecDet

variable {D : D7} (X : TermTie D)

def b1T' {u : D.what₂.Word} (t : D.s.Term u u) : ℕ :=
  idx (hS D) (XLam (X.abelian₂ t) (X.fl' t))
    ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl' t) (LatticeIndexAndWeightTheory.jOf X t))) ⊔ (X.abelian₂ t ⊓ toO (hS D) (LatticeIndexAndWeightTheory.Iof X t)))

def FrameDeterminantBound {u : D.what₂.Word} (t : D.s.Term u u) : Prop :=
  latDet (hS D) ((X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl t) (LatticeIndexAndWeightTheory.jOf X t))) ⊔
    (X.abelian₂ t ⊓ toO (hS D) (Xflag (X.fl' t) (LatticeIndexAndWeightTheory.jOf X t)))) ≤ LatticeIndexAndWeightTheory.DelJ X t

def BOneComparison {u : D.what₂.Word} (t : D.s.Term u u) : Prop := LatticeIndexAndWeightTheory.b1T X t ≤ b1T' X t

end RecDet

def DetBound : Prop :=
  ∀ {D : D7} (X : TermTie D) (u : D.what₂.Word), LatticeIndexAndWeightTheory.TieOK X u →
    ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → FrameDeterminantBound X t

def IdxLe : Prop :=
  ∀ {D : D7} (X : TermTie D) (u : D.what₂.Word), LatticeIndexAndWeightTheory.TieOK X u →
    ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → BOneComparison X t

end PI.TripleFrameDeterminant

end
