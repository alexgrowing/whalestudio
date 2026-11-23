import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariablesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromITailExponentialDecayStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionPropertiesStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerLimit

theorem trunc_mem (w : ℕ) (R : ℂ[X]) :
    (∑ j ∈ Finset.range (w + 1), C (R.coeff j) * X ^ j) ∈ degreeLT ℂ (w + 1) := by
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Finset.mem_range.1 hj

theorem trunc_coeff (w : ℕ) (R : ℂ[X]) {j : ℕ} (hj : j ≤ w) :
    (∑ i ∈ Finset.range (w + 1), C (R.coeff i) * X ^ i).coeff j = R.coeff j := by
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_of_le hj]

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  unfold eichler
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Finset.mem_range.1 hj

theorem bound_rate {F : ℍ → ℂ} {C c c' : ℝ} (hc : c' ≤ c)
    (hF : ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) :
    ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ max C 0 * Real.exp (-c' * τ.im) := by
  intro τ hτ
  refine (hF τ hτ).trans ?_
  have h1 : Real.exp (-c * τ.im) ≤ Real.exp (-c' * τ.im) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg (sub_nonneg.2 hc) (τ.im_pos.le)])
  calc C * Real.exp (-c * τ.im) ≤ max C 0 * Real.exp (-c * τ.im) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (-c' * τ.im) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

theorem polySlash_eichler_limit : ∀ (k : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]) (σ : SL(2, ℤ)) (Cf cf Ch ch : ℝ), 2 ≤ k → 0 < cf → 0 < ch → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[(k : ℤ)] σ) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h ∣[(k : ℤ)] σ) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(f ∣[(k : ℤ)] σ) τ‖ ≤ Cf * Real.exp (-cf * τ.im)) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(h ∣[(k : ℤ)] σ) τ‖ ≤ Ch * Real.exp (-ch * τ.im)) → p ∈ degreeLT ℂ (k - 1) → ∃ (Q : ℂ[X]) (C' c : ℝ), Q ∈ degreeLT ℂ (k - 2 + 1) ∧ 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ k - 2, ‖(slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p) - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (k - 2) := by
  intro k f h p σ Cf cf Ch ch hk hcf hch hf hh hfs hhs bf bh _hp
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk f hf σ
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk h hh σ
  have hc : 0 < min cf ch := lt_min hcf hch
  obtain ⟨Lf, Kf, hLf⟩ := GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay (k - 2) (f ∣[(k : ℤ)] σ) (max Cf 0) (min cf ch) hfs hc
    (bound_rate (min_le_left _ _) bf)
  obtain ⟨Lh, Kh, hLh⟩ := GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay (k - 2) (h ∣[(k : ℤ)] σ) (max Ch 0) (min cf ch) hhs hc
    (bound_rate (min_le_right _ _) bh)
  set R : ℂ[X] := Lf + C1 - (Lh + C2).map (starRingEnd ℂ) - slP (k - 2) (mat σ) p with hR
  refine ⟨∑ j ∈ Finset.range (k - 2 + 1), C (R.coeff j) * X ^ j, Kf + Kh, min cf ch,
    trunc_mem _ _, hc, ?_⟩
  intro τ hτ j hj
  have key : slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p)
      = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C1
        - (eichler (k - 2) (h ∣[(k : ℤ)] σ) τ + C2).map (starRingEnd ℂ) - slP (k - 2) (mat σ) p := by
    rw [map_sub, map_sub, hC1, ← (GlobalTheory.T.polyDegreeSlashAction_right_action_properties (k - 2) (mat σ) 1 _ (eichler_mem _ _ _)).2.2.2, hC2]
  have e1 := hLf τ hτ j hj
  have e2 := hLh τ hτ j hj
  rw [coeff_sub] at e1 e2
  rw [coeff_sub, key, trunc_coeff _ _ hj, hR]
  simp only [coeff_sub, coeff_add, coeff_map, map_add]
  calc _ = ‖((eichler (k - 2) (f ∣[(k : ℤ)] σ) τ).coeff j - Lf.coeff j)
        - (starRingEnd ℂ) ((eichler (k - 2) (h ∣[(k : ℤ)] σ) τ).coeff j - Lh.coeff j)‖ := by
          congr 1; rw [map_sub]; ring
    _ ≤ _ := norm_sub_le _ _
    _ = ‖(eichler (k - 2) (f ∣[(k : ℤ)] σ) τ).coeff j - Lf.coeff j‖
        + ‖(eichler (k - 2) (h ∣[(k : ℤ)] σ) τ).coeff j - Lh.coeff j‖ := by rw [Complex.norm_conj]
    _ ≤ _ := by rw [add_mul, add_mul]; exact add_le_add e1 e2

end GlobalTheory.EichlerLimit
