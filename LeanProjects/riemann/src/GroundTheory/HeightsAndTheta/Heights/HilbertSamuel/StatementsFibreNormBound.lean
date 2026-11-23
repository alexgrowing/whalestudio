import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (df : K → ℕ) (f : MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    IsMultiHomog f df → f ∉ mCoordIdeal y →
    ∃ (n c : ℕ) (B : ℝ) (G : MvPolynomial (Fin (D + 1)) ℤ)
      (Fib : (Fin (D + 1) → ℂ) → Finset ((Σ k, ι k) → ℂ)),
      1 ≤ n ∧ 1 ≤ B ∧ G ≠ 0 ∧
      (∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∀ z ∈ Fib ζ, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0) ∧
      ∀ τ : ℕ, ∀ u ∈ chartLatNm y A.a τ, u ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ (∀ i, F.degreeOf i ≤ c * (τ + 1)) ∧
          ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ Fib ζ, ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
              (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧ aeval y g = u * aeval y h ∧
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
              ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                M * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * M ^ n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
