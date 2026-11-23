import Mathlib
import Formalism.RealPlaceAnalysis.Complexify

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def reim {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) : EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
  (WithLp.equiv 2 (Fin n × Fin m × Bool → ℝ)).symm fun p => if p.2.2 then (Y p.1 p.2.1).re else (Y p.1 p.2.1).im

def PlaceJac : Prop := ∀ (n m : ℕ) (ε : Fin n → Bool) (S : Finset (Fin n)) (w : Matrix (Fin n) (Fin m) ℂ)
    {ι η : Type} [Fintype ι] [Fintype η]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ),
    n = m + S.card → (∀ i ∈ S, ∀ b, w i b = 0) → (wᴴ * Formalism.REAL.Jm ε * w).det ≠ 0 →
    (∀ x, (L x)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * L x = 0 ∧ ∀ i ∈ S, ∀ j ∈ S, L x i j = 0) →
    (∀ x, ∑ i, ∑ j, ‖L x i j‖ ^ 2 = ‖x‖ ^ 2) →
    (∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 →
      (∀ i ∈ S, ∀ j ∈ S, M i j = 0) → ∃ x, L x = M) →
    (∀ t, (H t)ᴴ = H t) → (∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) →
    (∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) →
    (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map
        (fun z => reim (L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2))) =
      ENNReal.ofReal (2 ^ (n * m) / ‖(wᴴ * Formalism.REAL.Jm ε * w).det‖ ^ S.card) • volume

end PI.AprimeInfW
