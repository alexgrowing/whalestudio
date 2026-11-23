import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.GenWh

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev IM (X : Loc) := (Σ j : Fin (numSeg X.TT), Fin (segS X.TT j)) ⊕
  ((Σ j : Fin (numSeg X.TT), Fin (segS X.TT j) × Fin X.m) ⊕ ((Σ j : Fin (numSeg X.TT), Fin (segS X.TT j)) ⊕ Fin X.m))

def multMk (X : Loc) (β : GlobalTheory X) : IM X → ℕ
  | Sum.inl x => (β x.1).sg x.2
  | Sum.inr (Sum.inl x) => (β x.1).rz x.2.1 x.2.2.succ
  | Sum.inr (Sum.inr (Sum.inl x)) => (β x.1).ry x.2 0
  | Sum.inr (Sum.inr (Sum.inr _)) => X.c

def fMk (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → RHH O X
  | Sum.inl x => kSkey O X x.1 x.2 ^ (X.seg C0 CE1 CE2 x.1).P X.p x.2
  | Sum.inr (Sum.inl x) => kWkey O X x.1 x.2.1 x.2.2.succ
  | Sum.inr (Sum.inr (Sum.inl x)) => kSkey O X x.1 x.2
  | Sum.inr (Sum.inr (Sum.inr c)) => locC O X c.succ

def aMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → MonH X
  | Sum.inl x => Finsupp.single ((topStart X x.1, true), 0) (X.p ^ segG X.TT x.1) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
  | Sum.inr (Sum.inl x) => Finsupp.single ((topOdd X x.1 x.2.1, true), x.2.2.succ) 1 +
      Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2.1)
  | Sum.inr (Sum.inr (Sum.inl x)) => Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) 1
  | Sum.inr (Sum.inr (Sum.inr _)) => ∑ j : Fin (numSeg X.TT), Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j - 1)

def oMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → ℕ
  | Sum.inl x => (X.seg C0 CE1 CE2 x.1).P X.p x.2
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

def dgMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → X.TT × Bool → ℕ
  | Sum.inl x => fun l => (X.seg C0 CE1 CE2 x.1).P X.p x.2 * dgKS X x.1 x.2 l
  | Sum.inr (Sum.inl x) => dgKW X x.1 x.2.1
  | Sum.inr (Sum.inr (Sum.inl x)) => dgKS X x.1 x.2
  | Sum.inr (Sum.inr (Sum.inr _)) => dgLoc X

def bMk (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j * (∑ i : Fin (segS X.TT j), (β j).sg i) +
      (∑ i : Fin (segS X.TT j), X.p ^ (segDists X.TT j).get i * ((∑ c : Fin X.m, (β j).rz i c.succ) + (β j).ry i 0)) +
      X.c * (X.m * (X.p ^ segG X.TT j - 1))) +
    (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, false), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0)) +
    ∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ)

end Formalism.MainNotions.ColumnSystems.Pf
