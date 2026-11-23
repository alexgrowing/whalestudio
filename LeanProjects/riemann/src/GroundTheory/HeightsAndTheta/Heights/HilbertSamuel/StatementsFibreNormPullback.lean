import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormMax
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormPullback.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ (n : ℕ) (M₀ : ℝ), 1 ≤ n ∧ 1 ≤ M₀ ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, s ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ F.IsHomogeneous (n * q * τ) ∧
          ∀ ζ : Fin (D + 1) → ℂ, ζ ≠ 0 →
          ∀ S : Finset ((Σ k, ι k) → ℂ),
            (∀ z ∈ mcPts (mCoordIdeal y),
              (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
              ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p) →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ S, z ∈ mcPts (mCoordIdeal y) →
              ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
                (∀ k, dg k = dh k + τ * (q * e k)) ∧ aeval y g = s * aeval y h ∧
                eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
                ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                  M * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ ^ (q * τ) *
                    ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ M₀ ^ τ * ‖ζ‖ ^ (n * q * τ) * M ^ n

open ProjLine in

theorem FibreNormPullback.hyps_inhabited :
    (IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y) ∧
    (∀ k : Unit, 1 ≤ (fun _ : Unit => 1) k) ∧
      (∀ j : Fin 2, IsMultiHomog (X ⟨(), j⟩ : MRing (GlobalTheory (Fin 2))) (fun _ => 1)) ∧
      ∀ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y), ∃ j : Fin 2,
        eval z (map (Int.castRingHom ℂ) (X ⟨(), j⟩ : MRing (GlobalTheory (Fin 2)))) ≠ 0 :=
  ⟨FibreNormMax.hyps_inhabited, FibreNormMax.coords_inhabited⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
