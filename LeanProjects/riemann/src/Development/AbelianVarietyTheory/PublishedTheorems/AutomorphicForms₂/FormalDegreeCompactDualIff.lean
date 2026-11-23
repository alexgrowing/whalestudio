import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

open Formalism.BasicNotions Formalism.MainNotions.S MeasureTheory

namespace GlobalTheory.Published

def FormalDegreeCompactDual : Prop :=
  ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ),
      (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((N : ℝ) - 1) / 2 = (m : ℝ)) →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        ‖w‖ ^ 4 / ∫ g, ‖inner ℂ w (σ (umat g) w)‖ ^ 2 ∂((sc N ε : ENNReal) • Formalism.REAL.muG ε) =
          (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b : Fin N => a < b), |lam a - lam b|) /
            ∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b : Fin N => a < b),
              (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

theorem formalDegreeCompactDual_iff : FormalDegreeCompactDual ↔ GlobalTheory.Mem.Vol.FormalDegreeFormula₂ := Iff.rfl

end GlobalTheory.Published
