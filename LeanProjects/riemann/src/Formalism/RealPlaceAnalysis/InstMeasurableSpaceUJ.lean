import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower

open MeasureTheory

noncomputable section

namespace Formalism.REAL

instance instLocallyCompactUJ (n : ℕ) (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) :=
  uJLocCompact_of isClosedEmbeddingMatrix n ε

instance instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) : MeasurableSpace (UJ ε) := borel _

instance instBorelSpaceUJ (n : ℕ) (ε : Fin n → Bool) : BorelSpace (UJ ε) := ⟨rfl⟩

instance instSecondCountableUJ (n : ℕ) (ε : Fin n → Bool) : SecondCountableTopology (UJ ε) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isClosedEmbeddingMatrix n ε).1.isInducing.secondCountableTopology

def muG {n : ℕ} (ε : Fin n → Bool) : Measure (UJ ε) := Measure.haar

instance instIsHaarMuG (n : ℕ) (ε : Fin n → Bool) : (muG ε).IsHaarMeasure := by
  unfold muG; infer_instance

def hsG {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : ℝ :=
  hs ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def Unimodular : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε), Measure.map (fun x => x * g) (muG ε) = muG ε

def InvInvariant : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), Measure.map (fun x : UJ ε => x⁻¹) (muG ε) = muG ε

def BallFinite : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : ℝ), muG ε {g | hsG g ≤ R} < ⊤

def BallPos : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : ℝ), (n : ℝ) < R → 0 < muG ε {g | hsG g < R}

def VolGrowth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
    muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2))

end Formalism.REAL
