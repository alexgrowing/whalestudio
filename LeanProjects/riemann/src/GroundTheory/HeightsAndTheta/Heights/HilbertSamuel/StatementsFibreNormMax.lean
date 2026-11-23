import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormMax.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ (n c : ℕ) (B : ℝ), 1 ≤ n ∧ 1 ≤ B ∧
      ∀ τ : ℕ, ∀ u ∈ chartLatNm y a τ, u ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ (∀ i, F.degreeOf i ≤ c * (τ + 1)) ∧
          ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) →
          ∀ S : Finset ((Σ k, ι k) → ℂ),
            (∀ z ∈ mcPts (mCoordIdeal y),
              (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
              ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p) →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ S, ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
              (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧ aeval y g = u * aeval y h ∧
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
              ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                M * (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) a).h z ^ τ *
                  ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * M ^ n

open ProjLine in

theorem FibreNormMax.coords_inhabited :
    (∀ k : Unit, 1 ≤ (fun _ : Unit => 1) k) ∧
      (∀ j : Fin 2, IsMultiHomog (X ⟨(), j⟩ : MRing (GlobalTheory (Fin 2))) (fun _ => 1)) ∧
      ∀ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y), ∃ j : Fin 2,
        eval z (map (Int.castRingHom ℂ) (X ⟨(), j⟩ : MRing (GlobalTheory (Fin 2)))) ≠ 0 := by
  classical
  refine ⟨fun _ => le_rfl, fun j m hm k => ?_, fun z hz => ?_⟩
  · rw [support_X, Finset.mem_singleton] at hm
    subst hm
    fin_cases j <;> simp [Finsupp.single_apply]
  · obtain ⟨i, hi⟩ := hz.1 ()
    exact ⟨i, by simpa using hi⟩

open ProjLine in

theorem FibreNormMax.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y :=
  ⟨isArithVar_y', birational_y⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
