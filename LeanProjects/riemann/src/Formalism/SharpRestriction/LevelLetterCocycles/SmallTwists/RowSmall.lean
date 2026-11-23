import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

noncomputable section

namespace Formalism.MainNotions.N.RowSmall

open Formalism.BasicNotions NumberField

variable {D : D7}

def sl (D : D7) (l : ℕ) : ℕ := max 1 (D.host.condN.factorization l)

def hB (L : SizeData₂ D) : ℝ := L.sc.b + L.Sc + L.etaSz + D.R.t + 2

def abelian₂ (L : SizeData₂ D) (l : ℕ) : ℝ := (sl D l : ℝ) + Real.logb l (2 * hB L) + 1

def cost (L : SizeData₂ D) (l : ℕ) : ℝ :=
  90 * D.R.f * D.R.m * hB L * (sl D l : ℝ) + 66 * (D.R.f : ℝ) ^ 2 * (D.R.t : ℝ) ^ 2 * D.R.nV * abelian₂ L l

def SplitInK (D : D7) (l : ℕ) : Prop := l ≠ 2 ∧ jacobiSym (-(D.host.d : ℤ)) l = 1

def ShaFinAt (D : D7) (l : ℕ) : Prop :=
  ∀ [Fact l.Prime] (e : ℕ), 0 < e → e < D.R.t → Formalism.GaloisCohomology.shaLen (D.nd.ldat l) (e : ℤ) ≠ ⊤

def TwistSmall (D : D7) (i : D.nd.Loc) : Prop :=
  (D.R.t : ℝ) * ∑ P ∈ D.nd.Q i, Formalism.MainNotions.BlochKatoReduction.Gen.tameVal (D := D) (N := D.nd) (D.nd.l i) (D.ntw.psiL i) (D.nd.plOm.1 P) ≤
    1 / (D.nd.l i : ℝ) ^ 2

def RowSplitAt (L : SizeData₂ D) (P : D.nd.Loc → Prop) (s : ∀ i : D.nd.Loc, D.nd.X i → ℝ) : Prop :=
  ∀ i : D.nd.Loc, D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0 → P i → SplitInK D (D.nd.l i) →
    D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ShaFinAt D (D.nd.l i) → TwistSmall D i → ∀ π ∈ D.nd.Zgood i,
      (D.nd.vcc i π : ℝ) ≤ cost L (D.nd.l i) + s i π + (D.what₂.VV (D.nd.l i) : ℝ) +
        (padicValNat (D.nd.l i) (Formalism.MainNotions.N.hE D.host) : ℝ) + 1 / (D.nd.l i : ℝ) ^ 2

def RowSplit (L : SizeData₂ D) (P : D.nd.Loc → Prop) : Prop :=
  RowSplitAt L P fun i _ => (padicValNat (D.nd.l i) (Units.torsionOrder D.host.E) : ℝ) + 1 / (D.nd.l i : ℝ) ^ 2

def RowSmallAt (L : SizeData₂ D) (A : D.nd.Loc → Prop) : Prop :=
  RowSplit L fun i => A i ∧ D.nd.l i ≠ 2 ∧ D.nd.l i ∈ D.host.small

end Formalism.MainNotions.N.RowSmall

end
