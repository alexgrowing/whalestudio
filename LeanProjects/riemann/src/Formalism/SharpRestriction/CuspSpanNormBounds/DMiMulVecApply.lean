import Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousCjIT

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Alg2

variable {k r : ℕ} {κ τ : ℝ}

theorem tV_eI (a : Fin r) : tV k r κ τ (eI k r a) = tF r κ τ a.val := by
  unfold tV eI; rw [if_pos a.isLt]

theorem tV_esI (a : Fin r) : tV k r κ τ (esI k r a) = (tF r κ τ a.val)⁻¹ := by
  unfold tV esI
  have h := a.isLt
  rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
  congr 2; simp only; omega

theorem tV_wb (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : tV k r κ τ i = 1 := by
  unfold tV; rw [if_neg (by omega), if_pos h2]

theorem dM_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dM k r κ τ *ᵥ v) i = ((tV k r κ τ i : ℝ) : ℂ) * v i := by
  rw [dM, Matrix.mulVec_diagonal]

theorem dMi_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dMi k r κ τ *ᵥ v) i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) * v i := by
  rw [dMi, Matrix.mulVec_diagonal]

theorem dM_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dM k r κ τ *ᵥ z = z := by
  funext i; rw [dM_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dMi_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dMi k r κ τ *ᵥ z = z := by
  funext i; rw [dMi_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dM_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dM k r κ τ *ᵥ bvec i = ((tV k r κ τ i : ℝ) : ℂ) • bvec i := by
  funext j; rw [dM_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem dMi_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dMi k r κ τ *ᵥ bvec i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) • bvec i := by
  funext j; rw [dMi_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem inWb_smul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : ℂ) : inWb k r (a • z) := by
  intro i hi; rw [Pi.smul_apply, hz i hi, smul_zero]

theorem cj_mulVec (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    cj k r κ τ x *ᵥ v = dMi k r κ τ *ᵥ (x *ᵥ (dM k r κ τ *ᵥ v)) := by
  rw [cj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem dM_mulVec_fvec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin (r + 1)) :
    dM k r κ τ *ᵥ fvec k r ((τ : ℂ) • z) a = ((tF r κ τ a.val : ℝ) : ℂ) • fvec k r z a := by
  unfold fvec
  by_cases h : a.val < r
  · rw [dif_pos h, dif_pos h, dM_mulVec_bvec, tV_eI]
  · rw [dif_neg h, dif_neg h, dM_mulVec_wb (inWb_smul hz _)]
    have : a.val = r := by omega
    simp [tF, this]

theorem ell_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Mx k r) :
    ell k r ((τ : ℂ) • z) (cj k r κ τ x) = (κ : ℂ)⁻¹ * ell k r z x := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a.val + 1 < r
  · rw [dif_pos h, dif_pos h, cj_apply, tV_eI, tV_eI]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have hk := pow_pos hκ (r - (a.val + 1))
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    have hkc : (κ : ℂ) ^ (r - (a.val + 1)) ≠ 0 := pow_ne_zero _ hκc
    simp only [tF]
    rw [e, pow_succ]
    push_cast
    field_simp
  · rw [dif_neg h, dif_neg h, cj_mulVec, dM_mulVec_wb (inWb_smul hz _), Matrix.mulVec_smul,
      dMi_mulVec_apply, tV_eI, Pi.smul_apply, smul_eq_mul]
    have e : r - a.val = 1 := by omega
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    simp only [tF, e, pow_one]
    push_cast
    field_simp

theorem psi_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (x : Mx k r) :
    psi k r ((τ : ℂ) • z) ((κ : ℂ) * c) (cj k r κ τ x) = psi k r z c x := by
  unfold psi
  rw [ell_cj hκ hτ hz]
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have : (κ : ℂ) * c * ((κ : ℂ)⁻¹ * ell k r z x) = c * ell k r z x := by
    field_simp
  rw [this]

theorem delta_iff {s y : ℂ} {i j : Fin (2 * r + k + 1)} (hs : s ≠ 0) (h1 : i = j → s = 1) :
    (s * y = if i = j then 1 else 0) ↔ (y = if i = j then 1 else 0) := by
  by_cases h : i = j
  · rw [h1 h, one_mul]
  · simp only [h, if_false, mul_eq_zero, hs, false_or]

theorem cj_fac_ne (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) ≠ 0 := by
  have := tV_pos (k := k) (r := r) hκ hτ i
  have := tV_pos (k := k) (r := r) hκ hτ j
  exact_mod_cast (mul_pos (inv_pos.mpr ‹0 < tV k r κ τ i›) this).ne'

theorem cj_fac_diag (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) (h : i = j) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) = 1 := by
  subst h; rw [inv_mul_cancel₀ (tV_pos hκ hτ i).ne']; simp

theorem cj_mem_Nset_iff (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) :
    cj k r κ τ x ∈ Nset k r ↔ x ∈ Nset k r := by
  simp only [Nset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ, cj_apply]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' fun a => forall_congr' fun i => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)
  · refine forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)

theorem UWset_smul {z : Fin (2 * r + k + 1) → ℂ} (hτ : 0 < τ) : UWset k r ((τ : ℂ) • z) = UWset k r z := by
  ext g
  simp only [UWset, Set.mem_ofPred_eq, Matrix.mulVec_smul]
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact smul_right_injective _ hτ' h

theorem cj_fix_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (hs : s ≠ 0)
    (h1 : dM k r κ τ *ᵥ v = s • v) (h2 : dMi k r κ τ *ᵥ v = s⁻¹ • v) :
    cj k r κ τ g *ᵥ v = v ↔ g *ᵥ v = v := by
  rw [cj_mulVec, h1, Matrix.mulVec_smul, Matrix.mulVec_smul]
  constructor
  · intro h
    have h3 : dM k r κ τ *ᵥ (s • (dMi k r κ τ *ᵥ (g *ᵥ v))) = dM k r κ τ *ᵥ v := by rw [h]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, dM_mul_dMi hκ hτ, Matrix.one_mulVec, h1] at h3
    exact smul_right_injective _ hs h3
  · intro h; rw [h, h2, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem cj_fix_bvec_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (i : Fin (2 * r + k + 1)) :
    cj k r κ τ g *ᵥ bvec i = bvec i ↔ g *ᵥ bvec i = bvec i := by
  refine cj_fix_iff hκ hτ g _ ((tV k r κ τ i : ℝ) : ℂ) (by exact_mod_cast (tV_pos hκ hτ i).ne')
    (dM_mulVec_bvec i) ?_
  rw [dMi_mulVec_bvec, Complex.ofReal_inv]

theorem cj_mem_UWset_iff (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mx k r) :
    cj k r κ τ g ∈ UWset k r z ↔ g ∈ UWset k r z := by
  simp only [UWset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ]
  refine and_congr Iff.rfl (and_congr (forall_congr' fun a =>
    and_congr (cj_fix_bvec_iff hκ hτ g _) (cj_fix_bvec_iff hκ hτ g _)) ?_)
  exact cj_fix_iff hκ hτ g z 1 one_ne_zero (by rw [one_smul, dM_mulVec_wb hz])
    (by rw [inv_one, one_smul, dMi_mulVec_wb hz])

theorem cj_mem_RStab_iff (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) :
    cj k r κ τ a ∈ RStab k r (cj k r κ τ g) ↔ a ∈ RStab k r g := by
  simp only [RStab, Set.mem_ofPred_eq]
  rw [← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, cj_mem_Nset_iff hκ hτ, cj_mem_Nset_iff hκ hτ]

end Alg2

end Formalism.MainNotions.FrameBoundFromBesselTorus
