import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

def OrthAt (C0 CE1 CE2 : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] (mm : ℝ), D1num X →
    ∀ (j : Fin (numSeg X.TT)) (b b' : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' → b ≠ b' →
      ∀ s ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b).SSZ O (r := X.m),
      ∀ s' ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b').SSZ O (r := X.m),
        fock (ioBlock (KK O) X.p C0 CE1 CE2 X j b s) (ioBlock (KK O) X.p C0 CE1 CE2 X j b' s') = 0

def ProdAt (C0 CE1 CE2 : ℝ) : Prop :=
  ∀ (X : Loc) (K : Type) [Field K], 2 ≤ numSeg X.TT → ∀ (β β' : GlobalTheory X)
    (s s' : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K),
    fock (symFam K X.p C0 CE1 CE2 X β s) (symFam K X.p C0 CE1 CE2 X β' s') =
      ∏ j, fock (ioBlock K X.p C0 CE1 CE2 X j (β j) (s j)) (ioBlock K X.p C0 CE1 CE2 X j (β' j) (s' j))

def SymPolAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (mm : ℝ) (β : GlobalTheory X), KeptAll C0 CE1 CE2 X β → ∀ s : Syms O C0 CE1 CE2 X, InSSZ O C0 CE1 CE2 mm X β s →
      symFam (KK O) X.p C0 CE1 CE2 X β s ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT)

def IntAt : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O], p.Prime → UniformizedDVR p O → ∀ (w : O)
    (n' m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ),
    ∀ P ∈ Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT),
    ∀ (Q : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (i : ℕ), InWj w P i → InA (O := O) Q →
      ∃ y : O, zTen (KK O) p m TT aT bT * fock P Q = algebraMap O (KK O) (w ^ i * y)

def NumAt (C0 Cde CE1 CE2 : ℝ) : Prop :=
  ∀ X : Loc, Std C0 Cde CE1 CE2 1 X → ∑ j : Fin (numSeg X.TT), (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ≤ 4 * X.kap0

def ZProdAt : Prop :=
  ∀ (X : Loc) (K : Type) [Field K], 2 ≤ numSeg X.TT → zTen K X.p X.m X.TT X.aT X.bT = ∏ j, zSeg K X j

end Formalism.MainNotions.ColumnSystems.Pf
