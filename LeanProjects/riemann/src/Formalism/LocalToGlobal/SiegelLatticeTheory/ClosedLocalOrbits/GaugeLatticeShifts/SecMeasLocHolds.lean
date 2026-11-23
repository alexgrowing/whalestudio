import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ZhatOfImages

noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

private theorem SecMeasLoc_holds_lemma {n : ℕ} (ε : Fin n → Bool) (x y v : Fin n → ℂ) :
    hJ ε (x - y) v = hJ ε x v - hJ ε y v := by
  simp only [hJ, star_sub, sub_dotProduct]

private theorem SecMeasLoc_holds_lemma_3 {n : ℕ} (ε : Fin n → Bool) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsIsom ε A) (hB : IsIsom ε B) : IsIsom ε (A * B) := by
  intro x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hB]

private theorem SecMeasLoc_holds_lemma_4 {n r : ℕ} (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (s : Fin r → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hep : ∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0)
    (hpp : ∀ a b, hJ ε (p a) (p b) = 0) :
    IsIsom ε (tvm ε (fun b => e b + s b • p b) (fun b => ((starRingEnd ℂ) (s b))⁻¹)) := by
  have hpe : ∀ a b, hJ ε (p a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hJ_cj, hep b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  apply tvm_isIsom
  · intro a b hab
    simp only [hJ_add_l, hJ_add_r, hJ_smul_l, hJ_smul_r, hee, hpp, hep, hpe, if_neg hab, if_neg (Ne.symm hab)]
    simp
  · intro b
    simp only [hJ_add_l, hJ_add_r, hJ_smul_l, hJ_smul_r, hee, hpp, hep, hpe, if_pos rfl, if_true, mul_one,
      mul_zero, zero_add, add_zero]
    by_cases hs : s b = 0
    · simp [hs]
    · have hc : (starRingEnd ℂ) (s b) ≠ 0 := (map_ne_zero _).mpr hs
      rw [map_inv₀, Complex.conj_conj]
      field_simp
      ring

private theorem SecMeasLoc_holds_lemma_5 {n r : ℕ} (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (s : Fin r → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hep : ∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0)
    (a : Fin r) (hs : s a ≠ 0) :
    tvm ε (fun b => e b + s b • p b) (fun b => ((starRingEnd ℂ) (s b))⁻¹) *ᵥ e a = -(s a • p a) := by
  have hpe : ∀ a b, hJ ε (p a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hJ_cj, hep b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have h1 : ((starRingEnd ℂ) (s a))⁻¹ * hJ ε (e a + s a • p a) (e a) = 1 := by
    have hc : (starRingEnd ℂ) (s a) ≠ 0 := (map_ne_zero _).mpr hs
    simp only [hJ_add_l, hJ_smul_l, hee, hpe, if_pos rfl, if_true, mul_one, zero_add]
    field_simp
  have h2 : ∀ b, b ≠ a → hJ ε (e b + s b • p b) (e a) = 0 := by
    intro b hb
    simp only [hJ_add_l, hJ_smul_l, hee, hpe, if_neg hb]
    simp
  rw [tvm_one ε (fun b => e b + s b • p b) (fun b => ((starRingEnd ℂ) (s b))⁻¹) a h1 h2]
  abel

private theorem SecMeasLoc_holds_lemma_6 {n r : ℕ} (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (s : Fin r → ℂ)
    (v : Fin n → ℂ) (hev : ∀ b, hJ ε (e b) v = 0) (hpv : ∀ b, hJ ε (p b) v = 0) :
    tvm ε (fun b => e b + s b • p b) (fun b => ((starRingEnd ℂ) (s b))⁻¹) *ᵥ v = v := by
  apply tvm_fix
  intro b
  simp only [hJ_add_l, hJ_smul_l, hev, hpv]
  simp

private theorem SecMeasLoc_holds_lemma_7 {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (T T' : ℝ) (hez : ∀ a, hJ ε (e a) z = 0) (hez' : ∀ a, hJ ε (e a) z' = 0)
    (hzz : hJ ε z z = -(T:ℂ)) (hzz' : hJ ε z' z' = -(T':ℂ)) (hT : 0 < T) (hT' : 0 < T') :
    ∃ σ : ℝ, σ ^ 2 * T = T' ∧ σ ≠ 0 ∧ ∃ K : Matrix (Fin n) (Fin n) ℂ,
      IsIsom ε K ∧ (∀ b, K *ᵥ e b = e b) ∧ K *ᵥ z' = (σ:ℂ) • z := by
  have key : ∀ σ : ℝ, σ ^ 2 * T = T' → σ ≠ 0 → hJ ε (z' - (σ:ℂ) • z) z' ≠ 0 →
      ∃ σ' : ℝ, σ' ^ 2 * T = T' ∧ σ' ≠ 0 ∧ ∃ K : Matrix (Fin n) (Fin n) ℂ,
        IsIsom ε K ∧ (∀ b, K *ᵥ e b = e b) ∧ K *ᵥ z' = (σ':ℂ) • z := by
    intro σ hσ hσ0 hD
    refine ⟨σ, hσ, hσ0, tv ε (z' - (σ:ℂ) • z) (hJ ε (z' - (σ:ℂ) • z) z')⁻¹, ?_, ?_, ?_⟩
    · apply step_isIsom
      rw [hzz', hJ_smul_l, hJ_smul_r, hzz, Complex.conj_ofReal]
      have h2 : (σ:ℂ) ^ 2 * T = T' := by exact_mod_cast hσ
      linear_combination h2
    · intro b
      have h0 : hJ ε (z' - (σ:ℂ) • z) (e b) = 0 := by
        rw [SecMeasLoc_holds_lemma, hJ_smul_l, hJ_zero_of_cj ε (hez' b), hJ_zero_of_cj ε (hez b)]
        simp
      rw [tv_apply, h0]
      simp
    · exact step_apply ε z' ((σ:ℂ) • z) hD
  have hs2 : Real.sqrt (T' / T) ^ 2 * T = T' := by
    rw [Real.sq_sqrt (div_nonneg hT'.le hT.le)]
    exact div_mul_cancel₀ _ hT.ne'
  have hs0 : Real.sqrt (T' / T) ≠ 0 := (Real.sqrt_pos.mpr (div_pos hT' hT)).ne'
  by_cases hD : hJ ε (z' - (Real.sqrt (T' / T):ℂ) • z) z' = 0
  · apply key (-Real.sqrt (T' / T)) (by rw [neg_sq]; exact hs2) (neg_ne_zero.mpr hs0)
    intro hD'
    rw [SecMeasLoc_holds_lemma, hJ_smul_l, Complex.conj_ofReal, hzz'] at hD hD'
    push_cast at hD'
    have h3 : (2:ℂ) * -(T':ℂ) = 0 := by linear_combination hD + hD'
    have hT'c : (T':ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
    apply hT'c
    linear_combination -h3 / 2
  · exact key _ hs2 hs0 hD

theorem SecMeasLoc_holds : SecMeasLoc := by
  intro n r k ε e z z' T T' sc hF hsc
  have hT := hF.T_pos
  have hT' := hF.T'_pos
  have hzz0 : hJ ε z z ≠ 0 := by
    rw [hF.zz]
    exact neg_ne_zero.mpr (by exact_mod_cast hT.ne')
  obtain ⟨p, hep, hpp, hzp⟩ := partner_exists ε e z hF.e_li hF.ee hF.ez hzz0
  obtain ⟨w, hww, hew, hpw, hzw⟩ :=
    scalar_frame_w_zero_exists ε k e p z T hF.dim hF.k_pos hF.sig hF.ee hep hpp hF.ez hzp hF.zz hT
  obtain ⟨σ, hσ, hσ0, K, hK, hKe, hKz⟩ :=
    SecMeasLoc_holds_lemma_7 ε e z z' T T' hF.ez hF.ez' hF.zz hF.zz' hT hT'
  have hwz : hJ ε w z = 0 := hJ_zero_of_cj ε hzw
  have hσc : ((σ:ℂ)) ^ 2 * T = T' := by exact_mod_cast hσ
  let Bm : (Fin (r + 1) → ℂ) → Matrix (Fin n) (Fin n) ℂ := fun c =>
    tvm ε (fun b => e b + (-lamOf sc c b) • p b) (fun b => ((starRingEnd ℂ) (-lamOf sc c b))⁻¹)
  let y : (Fin (r + 1) → ℂ) → Fin n → ℂ := fun c => alOf T c • z + beOf T T' c • w
  let Rm : (Fin (r + 1) → ℂ) → Matrix (Fin n) (Fin n) ℂ := fun c =>
    if hJ ε (y c) (y c) = -(T':ℂ) then
      tv ε ((σ:ℂ) • z - y c) (hJ ε ((σ:ℂ) • z - y c) ((σ:ℂ) • z))⁻¹
    else 1
  have hB : ∀ c, IsIsom ε (Bm c) := fun c => SecMeasLoc_holds_lemma_4 ε e p _ hF.ee hep hpp
  have hR : ∀ c, IsIsom ε (Rm c) := by
    intro c
    dsimp only [Rm]
    split_ifs with h
    · apply step_isIsom
      rw [h, hJ_smul_l, hJ_smul_r, hF.zz, Complex.conj_ofReal]
      linear_combination -hσc
    · intro x x'
      simp
  have hM : ∀ c, IsIsom ε (Rm c * Bm c * K) := fun c =>
    SecMeasLoc_holds_lemma_3 ε _ _ (SecMeasLoc_holds_lemma_3 ε _ _ (hR c) (hB c)) hK
  refine ⟨fun c => toUJ ε (hM c), measurable_toUJ ε (fun c => Rm c * Bm c * K) hM ?_, ?_⟩
  · have hlam : ∀ b, Measurable fun c : Fin (r + 1) → ℂ => lamOf sc c b := by
      intro b
      unfold lamOf
      exact (measurable_pi_apply _).div_const _
    have hal : Measurable fun c : Fin (r + 1) → ℂ => alOf T c := by
      unfold alOf
      exact (measurable_pi_apply _).neg.div_const _
    have hbe : Measurable fun c : Fin (r + 1) → ℂ => beOf T T' c := by
      unfold beOf
      exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
        ((((measurable_pi_apply _).norm.pow_const 2).div_const _).sub_const _))
    have hy : ∀ l, Measurable fun c => y c l := by
      intro l
      simp only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (hal.mul measurable_const).add (hbe.mul measurable_const)
    have hS : MeasurableSet {c | hJ ε (y c) (y c) = -(T':ℂ)} :=
      measurableSet_eq_fun (meas_hJ ε y y hy hy) measurable_const
    have hu : ∀ l, Measurable fun c => ((σ:ℂ) • z - y c) l := by
      intro l
      simp only [Pi.sub_apply]
      exact measurable_const.sub (hy l)
    have hxi : Measurable fun c => (hJ ε ((σ:ℂ) • z - y c) ((σ:ℂ) • z))⁻¹ :=
      (meas_hJ ε (fun c => (σ:ℂ) • z - y c) (fun _ => (σ:ℂ) • z) hu (fun _ => measurable_const)).inv
    have hRm : ∀ i j, Measurable fun c => Rm c i j := by
      intro i j
      have h8 : (fun c => Rm c i j) = fun c => if hJ ε (y c) (y c) = -(T':ℂ) then
          tv ε ((σ:ℂ) • z - y c) (hJ ε ((σ:ℂ) • z - y c) ((σ:ℂ) • z))⁻¹ i j
          else (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
        funext c
        dsimp only [Rm]
        split_ifs <;> rfl
      rw [h8]
      exact Measurable.ite hS (meas_tv ε (fun c => (σ:ℂ) • z - y c) _ hu hxi i j) measurable_const
    have hBm : ∀ i j, Measurable fun c => Bm c i j := by
      intro i j
      refine meas_tvm ε (fun c b => e b + (-lamOf sc c b) • p b)
        (fun c b => ((starRingEnd ℂ) (-lamOf sc c b))⁻¹) ?_ ?_ i j
      · intro b l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact measurable_const.add ((hlam b).neg.mul measurable_const)
      · intro b
        exact (Complex.continuous_conj.measurable.comp (hlam b).neg).inv
    exact meas_mul (fun c => Rm c * Bm c) (fun _ => K) (meas_mul Rm Bm hRm hBm) (fun _ _ => measurable_const)
  · intro c hc
    obtain ⟨hc0, hG⟩ := hc
    have hGp := normSq_last_sub_pos_of_Gv_diagonal_pos T T' c hG
    have hx : 0 ≤ ‖c (Fin.last r)‖ ^ 2 / T - T' := by
      rw [div_sub' hT.ne']
      exact div_nonneg (by linarith) hT.le
    have hb : (starRingEnd ℂ) (beOf T T' c) * beOf T T' c = ((‖c (Fin.last r)‖ ^ 2 / T - T' : ℝ) : ℂ) := by
      unfold beOf
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]
    have ha : (starRingEnd ℂ) (alOf T c) * alOf T c = ((‖c (Fin.last r)‖ ^ 2 / T ^ 2 : ℝ) : ℂ) := by
      unfold alOf
      rw [map_div₀, map_neg, Complex.conj_ofReal, neg_div, neg_div, neg_mul_neg, div_mul_div_comm,
        Complex.conj_mul']
      push_cast
      ring
    have e1 : hJ ε (y c) (y c) = -(T:ℂ) * ((starRingEnd ℂ) (alOf T c) * alOf T c)
        + (starRingEnd ℂ) (beOf T T' c) * beOf T T' c := by
      simp only [y, hJ_add_l, hJ_add_r, hJ_smul_l, hJ_smul_r, hF.zz, hww, hzw, hwz]
      ring
    have hyy : hJ ε (y c) (y c) = -(T':ℂ) := by
      rw [e1, ha, hb]
      have hTc : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      push_cast
      field_simp
      ring
    have hRc : Rm c = tv ε ((σ:ℂ) • z - y c) (hJ ε ((σ:ℂ) • z - y c) ((σ:ℂ) • z))⁻¹ := if_pos hyy
    have hlam0 : ∀ b, lamOf sc c b ≠ 0 := by
      intro b
      unfold lamOf
      have hs : (sc:ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
      exact div_ne_zero (hc0 _) (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hs)) (inv_ne_zero (pow_ne_zero _ hs)))
    show Zhat ε (famSc sc e z) (famSc sc e z') (Rm c * Bm c * K) = diagonal c
    apply zhat_of_images ε e p z z' w T sc (beOf T T' c) hep hF.ez hzp hew hF.zz hzw hT.ne' hsc c
    · intro b
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hKe]
      have hBe : Bm c *ᵥ e b = lamOf sc c b • p b := by
        have h := SecMeasLoc_holds_lemma_5 ε e p (fun b => -lamOf sc c b) hF.ee hep b (neg_ne_zero.mpr (hlam0 b))
        rw [neg_smul, neg_neg] at h
        exact h
      rw [hBe, hRc, tv_apply]
      have h0 : hJ ε ((σ:ℂ) • z - y c) (lamOf sc c b • p b) = 0 := by
        rw [SecMeasLoc_holds_lemma]
        simp only [y, hJ_add_l, hJ_smul_l, hJ_smul_r, hzp, hJ_zero_of_cj ε (hpw b)]
        simp
      rw [h0]
      simp
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hKz]
      have hBz : Bm c *ᵥ ((σ:ℂ) • z) = (σ:ℂ) • z := by
        apply SecMeasLoc_holds_lemma_6
        · intro b
          rw [hJ_smul_r, hF.ez b, mul_zero]
        · intro b
          rw [hJ_smul_r, hJ_zero_of_cj ε (hzp b), mul_zero]
      rw [hBz, hRc, tv_apply]
      by_cases hD : hJ ε ((σ:ℂ) • z - y c) ((σ:ℂ) • z) = 0
      · have hTc : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
        have e2 : hJ ε ((σ:ℂ) • z - y c) ((σ:ℂ) • z) = (σ:ℂ) * T * ((starRingEnd ℂ) (alOf T c) - σ) := by
          rw [SecMeasLoc_holds_lemma]
          simp only [y, hJ_add_l, hJ_smul_l, hJ_smul_r, hF.zz, hwz, Complex.conj_ofReal]
          ring
        have hca : (starRingEnd ℂ) (alOf T c) = σ := by
          rw [e2] at hD
          have h5 : (σ:ℂ) * T ≠ 0 := mul_ne_zero (by exact_mod_cast hσ0) hTc
          exact sub_eq_zero.mp ((mul_eq_zero.mp hD).resolve_left h5)
        have hα : alOf T c = σ := by
          have h6 := congrArg (starRingEnd ℂ) hca
          rwa [Complex.conj_conj, Complex.conj_ofReal] at h6
        have hβ : beOf T T' c = 0 := by
          have h4 : (starRingEnd ℂ) (beOf T T' c) * beOf T T' c = 0 := by
            have h7 := hyy
            rw [e1, hα, Complex.conj_ofReal] at h7
            linear_combination h7 + hσc
          rcases mul_eq_zero.mp h4 with h | h
          · exact (map_eq_zero _).mp h
          · exact h
        rw [hD, _root_.inv_zero, zero_mul, zero_smul, sub_zero]
        show (σ:ℂ) • z = alOf T c • z + beOf T T' c • w
        rw [hα, hβ, zero_smul, add_zero]
      · rw [inv_mul_cancel₀ hD, one_smul, sub_sub_cancel]

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
