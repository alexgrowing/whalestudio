import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensPf
import Formalism.LocalRingCardinality.DataTies

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

def l1B (ε : Fin n → Bool) (r : ℝ) : Set (EL ε) := {t | ∑ i, ∑ j, ‖linT ε t i j‖ < r}

def L1BallDensity (ε : Fin n → Bool) : Prop :=
  Tendsto (fun r : ℝ => Formalism.REAL.muG ε (expC ε '' l1B ε r) / volume (l1B ε r)) (𝓝[>] (0 : ℝ))
    (𝓝 (ENNReal.ofReal (gaugeU ε)))

def L1BallMeasurable (ε : Fin n → Bool) : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ r : ℝ, r ≤ s → MeasurableSet (expC ε '' l1B ε r)

def LamVol {P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ lam : Measure (Formalism.BasicNotions.lieU P Q), Formalism.BasicNotions.IsOmegaLeb lam → ∀ r : ℝ,
      lam (Formalism.BasicNotions.ballU P Q r) = volume (l1B ε r)

def SetEq {P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ r : ℝ,
    {g : Formalism.BasicNotions.UpqT P Q | ∃ a ∈ expC ε '' l1B ε r, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)} =
      {g | ∃ X ∈ Formalism.BasicNotions.ballU P Q r,
        Formalism.BasicNotions.UpqT.mat g = NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}

def UpqIn {P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ g : Formalism.BasicNotions.UpqT P Q, ∃ a : Formalism.REAL.UJ ε, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)

end Formalism.MainNotions.S.Gauge
