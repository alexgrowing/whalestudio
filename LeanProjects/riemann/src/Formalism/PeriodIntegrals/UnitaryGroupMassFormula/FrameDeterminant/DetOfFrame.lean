import Formalism.PeriodIntegrals.TripleFrameDeterminant

noncomputable section

namespace PI.TripleFrameDeterminant.W

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DetOfFrame : Prop :=
  ∀ {D : D7} (X : TermTie D) {u : D.what₂.Word} (t : D.s.Term u u), LatticeIndexAndWeightTheory.FrameHyp X t →
    Formalism.MainNotions.S.Dl (X.fl t).fl (X.fl' t).fl (LatticeIndexAndWeightTheory.jOf X t) ≠ 0 → FrameDeterminantBound X t

def NFAll : Prop :=
  ∀ {D : D7} (X : TermTie D) (u : D.what₂.Word), LatticeIndexAndWeightTheory.TieOK X u →
    ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → LatticeIndexAndWeightTheory.NF X t

def DjOfNF : Prop :=
  ∀ {D : D7} (X : TermTie D) {u : D.what₂.Word} (t : D.s.Term u u), LatticeIndexAndWeightTheory.NF X t →
    Formalism.MainNotions.S.Dl (X.fl t).fl (X.fl' t).fl (LatticeIndexAndWeightTheory.jOf X t) ≠ 0

def IdxOfNF : Prop :=
  ∀ {D : D7} (X : TermTie D) (u : D.what₂.Word), LatticeIndexAndWeightTheory.TieOK X u →
    ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → LatticeIndexAndWeightTheory.NF X t → BOneComparison X t

end PI.TripleFrameDeterminant.W

end
