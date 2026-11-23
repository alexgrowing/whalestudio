import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.FixedUnitaryApplyFixedIndexRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HalfLeNormOneSub

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

lemma enn_nnnorm (z : ℂ) : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  first
  | exact (ofReal_norm_eq_enorm z).symm
  | (rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (norm_nonneg _)]; rfl)
  | simp

lemma ofReal_rpow_neg_anti {a b s : ℝ} (hs : 0 ≤ s) (hab : a ≤ b) :
    ENNReal.ofReal b ^ (-s) ≤ ENNReal.ofReal a ^ (-s) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hab) hs)

lemma continuous_tW {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι) : Continuous (tW q) := by
  show Continuous fun x : ι → ℂ => Real.sqrt (∑ i, if i = q then 0 else Complex.normSq (x i))
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ =>
    continuous_if_const _ (fun _ => continuous_const)
      (fun _ => Complex.continuous_normSq.comp (continuous_apply i)))

lemma measurable_PsiF {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι) (s : ℝ) :
    Measurable (PsiF p q s) := by
  have h1 : Measurable fun x : ι → ℂ => (1 : ℂ) - star (x p) / ((tW q x : ℝ) : ℂ) := by
    first
    | exact measurable_const.sub (((continuous_star.comp (continuous_apply p)).measurable).div
        (Complex.continuous_ofReal.comp (continuous_tW q)).measurable)
    | fun_prop
  show Measurable fun x : ι → ℂ => (‖(1 : ℂ) - star (x p) / ((tW q x : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ (-s)
  exact (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp h1)).pow_const _

variable {k : ℕ}

lemma inWb_iK (k : ℕ) : inWb k 0 (bvec (iK k)) := by
  intro i hi
  exfalso
  have := i.isLt
  rcases hi with h | h <;> omega

private lemma mulVec_bvec_eq_fun_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    M *ᵥ bvec j = fun i => M i j := by
  funext i
  first
  | simp [Matrix.mulVec, bvec, Pi.single_apply]
  | simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  | simp [Matrix.mulVec, Matrix.dotProduct, bvec, Pi.single_apply]

private lemma star_bvec_dotProduct_eq_apply {n : ℕ} (j : Fin n) (w : Fin n → ℂ) : star (bvec j) ⬝ᵥ w = w j := by
  first
  | (rw [dotProduct, Finset.sum_eq_single j]
     · simp [bvec]
     · intro b _ hb; simp [bvec, Pi.single_apply, hb]
     · simp)
  | (rw [Matrix.dotProduct, Finset.sum_eq_single j]
     · simp [bvec]
     · intro b _ hb; simp [bvec, Pi.single_apply, hb]
     · simp)
  | simp [bvec]

lemma Tz_iK (k : ℕ) : 0 < Tz k 0 (bvec (iK k)) := by
  have hKK : Hpk k 0 (iK k) (iK k) = -1 := by
    simp [Hpk, iK, wI]
  have hh : herm (Hpk k 0) (bvec (iK k)) (bvec (iK k)) = -1 := by
    unfold herm
    rw [mulVec_bvec_eq_fun_apply, star_bvec_dotProduct_eq_apply]
    exact hKK
  unfold Tz
  rw [hh]
  norm_num

lemma ae_mem_fixedUnitary {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) : ∀ᵐ x ∂ν, (Matrix.of x : Mat k 0) ∈ U0 k := by
  first
  | exact ae_iff.2 hν.conc
  | (rw [ae_iff]; convert hν.conc using 1)

lemma haar_univ_lt_top (hCW : CompactW) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) : ν Set.univ < ∞ := by
  obtain ⟨U, hU⟩ : ∃ U : Set (Mt k 0), U = U0 k := ⟨_, rfl⟩
  have hK : IsCompact U := by rw [hU]; exact hCW k 0 (bvec (iK k)) (inWb_iK k) (Tz_iK k)
  have hc : ν Uᶜ = 0 := by rw [hU]; exact hν.conc
  have h1 : ν U < ∞ := hν.finite_compact _ hK
  have h2 := measure_union_le (μ := ν) U Uᶜ
  rw [Set.union_compl_self, hc, add_zero] at h2
  exact lt_of_le_of_lt h2 h1

lemma lint_lmul {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {a : Mat k 0} (ha : a ∈ U0 k)
    {F : Mt k 0 → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x, F (lmulM a x) ∂ν = ∫⁻ x, F x ∂ν := by
  have hm : Measurable (lmulM (k := k) (r := 0) a) := by
    have hc : Continuous (lmulM (k := k) (r := 0) a) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      show Continuous fun x : Mt k 0 => (a * Matrix.of x) i j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      exact continuous_finset_sum _ fun l _ =>
        continuous_const.mul ((continuous_apply j).comp (continuous_apply l))
    exact hc.measurable
  rw [← lintegral_map hF hm, hν.left a ha]

private lemma iW_ne_iK' (hk : 1 ≤ k) : iW k ≠ iK k := by
  intro h
  have h' := congrArg Fin.val h
  simp [iW, iK, wI] at h'
  omega

lemma rot (hk : 1 ≤ k) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {φ : ℂ → ℝ≥0∞}
    (hφ : Measurable φ) (v : Fin (2 * 0 + k + 1) → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hvc : tW (iK k) v ^ 2 = Complex.normSq c) :
    ∫⁻ x, φ (((Matrix.of x)ᴴ *ᵥ v) (iW k)) ∂ν = ∫⁻ x, φ (star c * star (x (iW k) (iW k))) ∂ν := by
  have hWK := iW_ne_iK' hk
  have hcs : star c ≠ 0 := by
    intro h; apply hc; rw [← star_star c, h, star_zero]
  have hc2 : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  have hS0 : 0 ≤ ∑ i, (if i = iK k then (0:ℝ) else Complex.normSq (v i)) :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg]
  have hS : (∑ i, if i = iK k then (0:ℝ) else Complex.normSq (v i)) = Complex.normSq c := by
    rw [← hvc]; unfold tW; rw [Real.sq_sqrt hS0]
  obtain ⟨u, hudef⟩ : ∃ u : Fin (2 * 0 + k + 1) → ℂ,
      u = fun i => if i = iK k then 0 else (star c)⁻¹ * v i := ⟨_, rfl⟩
  have hu0 : u (iK k) = 0 := by rw [hudef]; simp
  have hterm : ∀ i, star (u i) * u i =
      (((if i = iK k then (0:ℝ) else Complex.normSq (v i)) / Complex.normSq c : ℝ) : ℂ) := by
    intro i
    rw [show star (u i) * u i = ((Complex.normSq (u i) : ℝ) : ℂ) from
      (Complex.normSq_eq_conj_mul_self).symm]
    congr 1
    by_cases h : i = iK k
    · simp [hudef, h]
    · simp only [hudef, h, if_false]
      rw [Complex.normSq_mul, Complex.normSq_inv,
        show Complex.normSq (star c) = Complex.normSq c from Complex.normSq_conj c]
      ring
  have hu1 : star u ⬝ᵥ u = 1 := by
    first
    | simp only [dotProduct, Pi.star_apply, hterm]
    | simp only [Matrix.dotProduct, Pi.star_apply, hterm]
    rw [← Complex.ofReal_sum, ← Finset.sum_div, hS, div_self hc2, Complex.ofReal_one]
  obtain ⟨R, hR, hRe⟩ := exists_fixedUnitary_sending_basis hk u hu0 hu1
  have hRv : Rᴴ *ᵥ v = star c • bvec (iW k) + v (iK k) • bvec (iK k) := by
    have hv : v = star c • u + v (iK k) • bvec (iK k) := by
      funext i
      by_cases h : i = iK k
      · subst h; simp [hudef, bvec]
      · rw [hudef]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_neg h, bvec, Pi.single_apply,
          mul_zero, add_zero]
        rw [mul_inv_cancel_left₀ hcs]
    have h1 : Rᴴ *ᵥ u = bvec (iW k) := by
      rw [← hRe, Matrix.mulVec_mulVec, (fixedUnitary_projection_identities hR).1, Matrix.one_mulVec]
    have h2 : Rᴴ *ᵥ bvec (iK k) = bvec (iK k) := by
      rw [mulVec_bvec_eq_fun_apply]
      ext i
      rw [fixedUnitary_apply_fixedIndex_right (fixedUnitary_conjTranspose_mem hR) i]
      simp [bvec, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2]
  have key : ∀ x : Mt k 0, (Matrix.of x : Mat k 0) ∈ U0 k →
      ((Matrix.of (lmulM R x))ᴴ *ᵥ v) (iW k) = star c * star (x (iW k) (iW k)) := by
    intro x hx
    have hx0 : x (iK k) (iW k) = 0 := by
      have h := fixedUnitary_apply_fixedIndex_left hx (iW k)
      rw [if_neg hWK] at h
      exact h
    show ((R * Matrix.of x)ᴴ *ᵥ v) (iW k) = _
    rw [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, hRv, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_bvec_eq_fun_apply, mulVec_bvec_eq_fun_apply]
    simp [Matrix.conjTranspose_apply, hx0]
  have hcont : Continuous (fun x : Mt k 0 => ((Matrix.of x)ᴴ *ᵥ v) (iW k)) := by
    first
    | (simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
       exact continuous_finset_sum _ fun j _ =>
        (continuous_star.comp ((continuous_apply (iW k)).comp (continuous_apply j))).mul
          continuous_const)
    | (simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
       exact continuous_finset_sum _ fun j _ =>
        (continuous_star.comp ((continuous_apply (iW k)).comp (continuous_apply j))).mul
          continuous_const)
    | fun_prop
  have hmeasF : Measurable (fun x : Mt k 0 => φ (((Matrix.of x)ᴴ *ᵥ v) (iW k))) :=
    hφ.comp hcont.measurable
  calc ∫⁻ x, φ (((Matrix.of x)ᴴ *ᵥ v) (iW k)) ∂ν
      = ∫⁻ x, φ (((Matrix.of (lmulM R x))ᴴ *ᵥ v) (iW k)) ∂ν := (lint_lmul hν hR hmeasF).symm
    _ = ∫⁻ x, φ (star c * star (x (iW k) (iW k))) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [ae_mem_fixedUnitary hν] with x hx
        rw [key x hx]

def C0 (k : ℕ) (s : ℝ) (ν : Measure (Mt k 0)) : ℝ≥0∞ :=
  ∫⁻ x, (‖1 - x (iW k) (iW k)‖₊ : ℝ≥0∞) ^ (-s) ∂ν

lemma norm_fixedUnitary_entry_le_one {h : Mat k 0} (hh : h ∈ U0 k) (i j : Fin (2 * 0 + k + 1)) : ‖h i j‖ ≤ 1 := by
  have h1 := congrFun (congrFun (fixedUnitary_projection_identities hh).1 j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
  have h2 : ∑ x, ((Complex.normSq (h x j) : ℝ) : ℂ) = 1 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  have h3 : ∑ x, Complex.normSq (h x j) = 1 := by exact_mod_cast h2
  have h4 : Complex.normSq (h i j) ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (f := fun x => Complex.normSq (h x j))
      (fun x _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at h4
  nlinarith [norm_nonneg (h i j)]

private lemma norm_one_sub_le_two_mul_norm_one_sub_real_mul {w : ℂ} {ρ : ℝ} (hw : ‖w‖ ≤ 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    ‖1 - w‖ ≤ 2 * ‖1 - (ρ : ℂ) * w‖ := by
  have hρw : ‖(ρ : ℂ) * w‖ = ρ * ‖w‖ := by
    rw [norm_mul]
    first
    | rw [Complex.norm_real, Real.norm_of_nonneg h0]
    | rw [Complex.norm_of_nonneg h0]
    | simp [abs_of_nonneg h0]
  have e : (1 : ℂ) - w = (1 - (ρ : ℂ) * w) + ((ρ : ℂ) - 1) * w := by ring
  have hA1 : ‖(1 : ℂ) - w‖ ≤ ‖1 - (ρ : ℂ) * w‖ + ‖((ρ : ℂ) - 1) * w‖ := by
    rw [e]; exact norm_add_le _ _
  have hA2 : ‖((ρ : ℂ) - 1) * w‖ = (1 - ρ) * ‖w‖ := by
    have e2 : (ρ : ℂ) - 1 = ((ρ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, e2]
    first
    | rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
    | (simp only [Complex.norm_real, Real.norm_eq_abs]; rw [abs_of_nonpos (by linarith)]; ring)
    | (rw [Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_nonpos (by linarith)]; ring)
  have hA3 : 1 - ρ * ‖w‖ ≤ ‖1 - (ρ : ℂ) * w‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((ρ : ℂ) * w)
    rwa [norm_one, hρw] at this
  nlinarith [norm_nonneg w, norm_nonneg ((1 : ℂ) - (ρ : ℂ) * w), mul_nonneg h0 (sub_nonneg.2 hw)]

lemma bnd (hk : 1 ≤ k) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {s : ℝ} (hs : 0 ≤ s)
    {lam : ℝ} (hlam : 0 < lam) (v : Fin (2 * 0 + k + 1) → ℂ) (b : ℂ) (hb : b ≠ 0)
    (hvb : tW (iK k) v ^ 2 ≤ Complex.normSq b) :
    ∫⁻ x, ENNReal.ofReal (lam * ‖((Matrix.of x)ᴴ *ᵥ v) (iW k) + b‖) ^ (-s) ∂ν ≤
      ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) * (C0 k s ν + ν Set.univ) := by
  have hWK := iW_ne_iK' hk
  have hb0 : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hA : 0 ≤ lam * ‖b‖ / 2 := div_nonneg (mul_nonneg hlam.le hb0.le) (by norm_num)
  obtain ⟨t, ht⟩ : ∃ t, t = tW (iK k) v := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.sqrt_nonneg _
  have htb : t ≤ ‖b‖ := by
    have h2 : t ^ 2 ≤ ‖b‖ ^ 2 := by rw [ht, ← Complex.normSq_eq_norm_sq]; exact hvb
    nlinarith
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (2 * 0 + k + 1))),
        0 ≤ (if i = iK k then (0:ℝ) else Complex.normSq (v i)) := fun i _ => by
      split_ifs <;> simp [Complex.normSq_nonneg]
    have hS : (∑ i, if i = iK k then (0:ℝ) else Complex.normSq (v i)) = 0 := by
      have h1 : tW (iK k) v = 0 := ht.symm.trans h0.symm
      unfold tW at h1
      have h2 := Real.sqrt_eq_zero'.mp h1
      linarith [Finset.sum_nonneg hnn]
    have hv0 : ∀ i, i ≠ iK k → v i = 0 := by
      intro i hi
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS i (Finset.mem_univ i)
      rw [if_neg hi] at h3
      exact Complex.normSq_eq_zero.mp h3
    calc ∫⁻ x, ENNReal.ofReal (lam * ‖((Matrix.of x)ᴴ *ᵥ v) (iW k) + b‖) ^ (-s) ∂ν
        = ∫⁻ _x, ENNReal.ofReal (lam * ‖b‖) ^ (-s) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [ae_mem_fixedUnitary hν] with x hx
          have hx0 : x (iK k) (iW k) = 0 := by
            have h := fixedUnitary_apply_fixedIndex_left hx (iW k)
            rw [if_neg hWK] at h
            exact h
          have hz : ((Matrix.of x)ᴴ *ᵥ v) (iW k) = 0 := by
            first
            | simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
            | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
            refine Finset.sum_eq_zero fun i _ => ?_
            by_cases hi : i = iK k
            · rw [hi, hx0, star_zero, zero_mul]
            · rw [hv0 i hi, mul_zero]
          rw [hz, zero_add]
      _ = ENNReal.ofReal (lam * ‖b‖) ^ (-s) * ν Set.univ := lintegral_const _
      _ ≤ ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) * ν Set.univ :=
          mul_le_mul_of_nonneg_right (ofReal_rpow_neg_anti hs (by linarith)) (zero_le ..)
      _ ≤ _ := mul_le_mul_of_nonneg_left le_add_self (zero_le ..)
  · have hρ0' : 0 < t / ‖b‖ := div_pos hpos hb0
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = t / ‖b‖ := ⟨_, rfl⟩
    have hρ0 : 0 ≤ ρ := by rw [hρ]; exact hρ0'.le
    have hρne : ρ ≠ 0 := by rw [hρ]; exact hρ0'.ne'
    have hρ1 : ρ ≤ 1 := by rw [hρ]; exact (div_le_one hb0).mpr htb
    obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = star (-(b * (ρ : ℂ))) := ⟨_, rfl⟩
    have hsc : star c = -(b * (ρ : ℂ)) := by rw [hcdef, star_star]
    have hc : c ≠ 0 := by
      intro h
      have h' : star c = 0 := by rw [h, star_zero]
      rw [hsc, neg_eq_zero] at h'
      exact mul_ne_zero hb (Complex.ofReal_ne_zero.mpr hρne) h'
    have hvc : tW (iK k) v ^ 2 = Complex.normSq c := by
      have e : Complex.normSq c = Complex.normSq (star c) := (Complex.normSq_conj c).symm
      have hbne : ‖b‖ ≠ 0 := hb0.ne'
      rw [e, hsc, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_eq_norm_sq, ← ht, hρ]
      field_simp
      try ring
    have hφ : Measurable (fun z : ℂ => ENNReal.ofReal (lam * ‖z + b‖) ^ (-s)) := by
      first
      | exact (ENNReal.continuous_ofReal.comp
          (continuous_const.mul (continuous_id.add continuous_const).norm)).measurable.pow_const _
      | fun_prop
    have hrot := rot hk hν hφ v c hc hvc
    refine hrot.trans_le ?_
    have hmeasC : Measurable (fun x : Mt k 0 => (‖1 - x (iW k) (iW k)‖₊ : ℝ≥0∞) ^ (-s)) := by
      first
      | exact (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp (measurable_const.sub
          ((measurable_pi_apply (iW k)).comp (measurable_pi_apply (iW k)))))).pow_const _
      | fun_prop
    have key : ∀ x : Mt k 0, (Matrix.of x : Mat k 0) ∈ U0 k →
        ENNReal.ofReal (lam * ‖star c * star (x (iW k) (iW k)) + b‖) ^ (-s) ≤
          ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) * (‖1 - x (iW k) (iW k)‖₊ : ℝ≥0∞) ^ (-s) := by
      intro x hx
      have hz : ‖x (iW k) (iW k)‖ ≤ 1 := norm_fixedUnitary_entry_le_one hx (iW k) (iW k)
      have hw : ‖star (x (iW k) (iW k))‖ ≤ 1 := by rw [norm_star]; exact hz
      have h4 := norm_one_sub_le_two_mul_norm_one_sub_real_mul hw hρ0 hρ1
      have h5 := mul_le_mul_of_nonneg_left h4 hA
      have e2 : star c * star (x (iW k) (iW k)) + b =
          b * (1 - (ρ : ℂ) * star (x (iW k) (iW k))) := by
        rw [hsc]; ring
      have e3 : ‖(1 : ℂ) - x (iW k) (iW k)‖ = ‖(1 : ℂ) - star (x (iW k) (iW k))‖ := by
        rw [← norm_star, star_sub, star_one]
      rw [enn_nnnorm, ← ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ← ENNReal.ofReal_mul hA]
      apply ofReal_rpow_neg_anti hs
      rw [e2, norm_mul, e3]
      nlinarith [norm_nonneg ((1 : ℂ) - (ρ : ℂ) * star (x (iW k) (iW k))), norm_nonneg b]
    calc ∫⁻ x, ENNReal.ofReal (lam * ‖star c * star (x (iW k) (iW k)) + b‖) ^ (-s) ∂ν
        ≤ ∫⁻ x, ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) *
            (‖1 - x (iW k) (iW k)‖₊ : ℝ≥0∞) ^ (-s) ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [ae_mem_fixedUnitary hν] with x hx
          exact key x hx
      _ = ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) * C0 k s ν := lintegral_const_mul _ hmeasC
      _ ≤ _ := mul_le_mul_of_nonneg_left le_self_add (zero_le ..)

private lemma nnnorm_one_sub_star_div_real_eq (z : ℂ) (t : ℝ) :
    ‖1 - star z / (t : ℂ)‖₊ = ‖1 - z / (t : ℂ)‖₊ := by
  have e : (1 : ℂ) - star z / (t : ℂ) = star (1 - z / (t : ℂ)) := by
    simp [star_div₀, Complex.conj_ofReal]
  rw [e, nnnorm_star]

lemma haarIntegralConstant_lt_top (hk : 1 ≤ k) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) (hνf : ν Set.univ < ∞)
    {s : ℝ} (hs : 0 ≤ s) (hsk : s < k) : C0 k s ν < ∞ := by
  classical
  have : IsFiniteMeasure ν := ⟨hνf⟩
  have hpq : iW k ≠ iK k := iW_ne_iK' hk
  have hcard : Fintype.card (Fin (2 * 0 + k + 1)) = k + 1 := by simp
  have hL := lint_Bset_lt_top hpq hcard hk hs hsk
  have hB0 := volume_Bset_ne_zero hpq hcard
  have hBm : MeasurableSet (Bset (iK k) : Set (Fin (2 * 0 + k + 1) → ℂ)) := measurableSet_Bset _

  let G : (Fin (2 * 0 + k + 1) → ℂ) → Mt k 0 → ℝ≥0∞ := fun x h =>
    (‖1 - ((Matrix.of h)ᴴ *ᵥ x) (iW k) / (tW (iK k) x : ℂ)‖₊ : ℝ≥0∞) ^ (-s)

  have hrot : ∀ x ∈ Bset (iK k), ∫⁻ h, G x h ∂ν = C0 k s ν := by
    intro x hx
    have ht : (1 : ℝ) / 2 ≤ tW (iK k) x := hx.1
    set c : ℂ := (tW (iK k) x : ℂ) with hcdef
    have hc : c ≠ 0 := by
      rw [hcdef]
      exact_mod_cast (ne_of_gt (by linarith : (0 : ℝ) < tW (iK k) x))
    have hvc : tW (iK k) x ^ 2 = Complex.normSq c := by
      rw [hcdef, Complex.normSq_ofReal]
      ring
    have hφ : Measurable fun z : ℂ => (‖1 - z / c‖₊ : ℝ≥0∞) ^ (-s) :=
      ((measurable_const.sub (measurable_id.div_const c)).nnnorm.coe_nnreal_ennreal).pow_const (-s)
    have hr := rot hk hν hφ x c hc hvc
    show ∫⁻ h, (fun z : ℂ => (‖1 - z / c‖₊ : ℝ≥0∞) ^ (-s)) (((Matrix.of h)ᴴ *ᵥ x) (iW k)) ∂ν = C0 k s ν
    rw [hr, C0]
    refine lintegral_congr fun h => ?_
    have hsc : star c = c := by rw [hcdef]; exact Complex.conj_ofReal _
    rw [hsc, mul_div_cancel_left₀ _ hc]
    have e : (1 : ℂ) - star (h (iW k) (iW k)) = star (1 - h (iW k) (iW k)) := by simp
    rw [e, nnnorm_star]

  have hinner : ∀ᵐ h ∂ν, ∫⁻ x in Bset (iK k), G x h = ∫⁻ x in Bset (iK k), PsiF (iW k) (iK k) s x := by
    filter_upwards [ae_mem_fixedUnitary hν] with h hh
    have hA : (Matrix.of h)ᴴ ∈ U0 k := fixedUnitary_conjTranspose_mem hh
    have hu := (fixedUnitary_projection_identities hA).1
    have htw := tW_mulVec hu (fixedUnitary_apply_fixedIndex_left hA)
    have hmp := mp_unitary _ hu
    have hpre : (fun x => (Matrix.of h)ᴴ *ᵥ x) ⁻¹' Bset (iK k) = Bset (iK k) := by
      ext x
      simp only [Set.mem_preimage, Bset, Set.mem_ofPred_eq, (htw x).1, (htw x).2]
    have hpt : ∀ x, G x h = PsiF (iW k) (iK k) s ((Matrix.of h)ᴴ *ᵥ x) := by
      intro x
      simp only [G, PsiF, (htw x).1]
      rw [nnnorm_one_sub_star_div_real_eq]
    simp only [hpt]
    rw [← hmp.setLIntegral_comp_preimage hBm (measurable_PsiF _ _ _), hpre]
  have hcont : Continuous fun p : (Fin (2 * 0 + k + 1) → ℂ) × Mt k 0 =>
      ((Matrix.of p.2)ᴴ *ᵥ p.1) (iW k) := by
    have h2 : Continuous fun p : (Fin (2 * 0 + k + 1) → ℂ) × Mt k 0 => (Matrix.of p.2 : Mat k 0) :=
      continuous_snd
    exact (continuous_apply _).comp (h2.matrix_conjTranspose.matrix_mulVec continuous_fst)
  have hden : Measurable fun p : (Fin (2 * 0 + k + 1) → ℂ) × Mt k 0 => (tW (iK k) p.1 : ℂ) :=
    (Complex.continuous_ofReal.comp ((continuous_tW (iK k)).comp continuous_fst)).measurable
  have hmeas : Measurable (Function.uncurry G) :=
    ((measurable_const.sub (hcont.measurable.div hden)).nnnorm.coe_nnreal_ennreal).pow_const (-s)
  have hswap := lintegral_lintegral_swap
    (hmeas.aemeasurable : AEMeasurable (Function.uncurry G) ((volume.restrict (Bset (iK k))).prod ν))
  have h1 : ∫⁻ x in Bset (iK k), ∫⁻ h, G x h ∂ν = C0 k s ν * volume (Bset (iK k)) := by
    rw [setLIntegral_congr_fun hBm hrot, lintegral_const, Measure.restrict_apply_univ]
  have h2 : ∫⁻ h, (∫⁻ x in Bset (iK k), G x h) ∂ν = (∫⁻ x in Bset (iK k), PsiF (iW k) (iK k) s x) * ν Set.univ := by
    rw [lintegral_congr_ae hinner, lintegral_const]
  have hfin : C0 k s ν * volume (Bset (iK k)) < ∞ := by
    rw [← h1, hswap, h2]
    exact ENNReal.mul_lt_top hL hνf
  rcases ENNReal.mul_lt_top_iff.1 hfin with h | h | h
  · exact h.1
  · rw [h]
    exact ENNReal.zero_lt_top
  · exact absurd h hB0

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
