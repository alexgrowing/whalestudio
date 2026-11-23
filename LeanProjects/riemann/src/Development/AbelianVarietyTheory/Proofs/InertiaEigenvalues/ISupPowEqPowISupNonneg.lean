import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

namespace Lead

theorem mono_lt {a C ρ₁ ρ₂ ρ : ℝ} {n : ℕ} {e : ℤ} (h1 : 0 < ρ₁) (hl : ρ₁ < ρ) (hr : ρ < ρ₂) (ha : 0 < a)
    (hne : (n : ℤ) ≠ e) (b1 : a * ρ₁ ^ n ≤ C * ρ₁ ^ e) (b2 : a * ρ₂ ^ n ≤ C * ρ₂ ^ e) :
    a * ρ ^ n < C * ρ ^ e := by
  have hρ : 0 < ρ := h1.trans hl
  have hρ2 : 0 < ρ₂ := hρ.trans hr
  set d : ℤ := (n : ℤ) - e with hd
  have key : ∀ t : ℝ, 0 < t → a * t ^ n = t ^ e * (a * t ^ d) := by
    intro t ht
    rw [← zpow_natCast, show (n : ℤ) = e + d by omega, zpow_add₀ ht.ne']
    ring
  have red : ∀ t : ℝ, 0 < t → a * t ^ n ≤ C * t ^ e → a * t ^ d ≤ C := by
    intro t ht h
    rw [key t ht, mul_comm C] at h
    exact le_of_mul_le_mul_left h (zpow_pos ht e)
  rw [key ρ hρ, mul_comm C]
  refine mul_lt_mul_of_pos_left ?_ (zpow_pos hρ e)
  rcases lt_or_gt_of_ne (show d ≠ 0 by omega) with hneg | hpos
  · have c1 := red ρ₁ h1 b1
    refine lt_of_lt_of_le (mul_lt_mul_of_pos_left ?_ ha) c1
    have e1 : ρ ^ d = (ρ ^ (-d))⁻¹ := by rw [zpow_neg, inv_inv]
    have e2 : ρ₁ ^ d = (ρ₁ ^ (-d))⁻¹ := by rw [zpow_neg, inv_inv]
    rw [e1, e2]
    exact inv_strictAnti₀ (zpow_pos h1 _) (zpow_lt_zpow_left₀ (by omega) h1.le hl)
  · have c2 := red ρ₂ hρ2 b2
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left (zpow_lt_zpow_left₀ hpos hρ.le hr) ha) c2

theorem iSup_lt {d : ℕ → ℝ} {ρ T : ℝ} (h0 : ∀ n, 0 ≤ d n) (h1 : ∀ n, d n ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hT : 0 < T) (h : ∀ n, d n * ρ ^ n < T) : (⨆ n, d n * ρ ^ n) < T := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hT hρ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.range (M + 1)) (fun n => d n * ρ ^ n)
    ⟨0, by simp⟩
  refine lt_of_le_of_lt (ciSup_le fun n => ?_ : (⨆ n, d n * ρ ^ n) ≤ max (d i * ρ ^ i) (ρ ^ M))
    (max_lt (h i) hM)
  by_cases hn : n < M + 1
  · exact le_max_of_le_left (hi n (Finset.mem_range.2 hn))
  · refine le_max_of_le_right ?_
    calc d n * ρ ^ n ≤ 1 * ρ ^ n := by gcongr; exact h1 n
      _ = ρ ^ n := one_mul _
      _ ≤ ρ ^ M := pow_le_pow_of_le_one hρ.le hρ1.le (by omega)

theorem lead (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ₁ ρ₂ C : ℝ} {e : ℤ} (hρ₁ : 0 < ρ₁)
    (h12 : ρ₁ < ρ₂) (hρ₂ : ρ₂ < 1) (hC : 0 < C) (hs : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, (⨆ n, c n * ρ ^ n) = C * ρ ^ e) :
    ∃ m : ℕ, (m : ℤ) = e ∧ c m = C ∧ ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, ∀ d : ℕ → ℝ, (∀ n, 0 ≤ d n) → (∀ n, d n ≤ c n) →
      d m = 0 → (⨆ n, d n * ρ ^ n) < C * ρ ^ e := by
  have hb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ∀ n, c n * ρ ^ n ≤ C * ρ ^ e := by
    intro ρ hρ n
    rw [← hs ρ hρ]
    have hρ0 : 0 ≤ ρ := hρ₁.le.trans hρ.1
    have hρ1 : ρ ≤ 1 := hρ.2.trans hρ₂.le
    refine le_ciSup (f := fun n => c n * ρ ^ n) ⟨1, Set.forall_mem_range.2 fun n => ?_⟩ n
    calc c n * ρ ^ n ≤ 1 * 1 := mul_le_mul (h1 n) (pow_le_one₀ hρ0 hρ1) (pow_nonneg hρ0 _) zero_le_one
      _ = 1 := one_mul 1
  have B : ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, ∀ d : ℕ → ℝ, (∀ n, 0 ≤ d n) → (∀ n, d n ≤ c n) →
      (∀ n : ℕ, (n : ℤ) = e → d n < C) → (⨆ n, d n * ρ ^ n) < C * ρ ^ e := by
    intro ρ hρ d hd0 hdc hde
    have hρ0 : 0 < ρ := hρ₁.trans hρ.1
    have hρ1 : ρ < 1 := hρ.2.trans hρ₂
    refine iSup_lt hd0 (fun n => (hdc n).trans (h1 n)) hρ0 hρ1 (mul_pos hC (zpow_pos hρ0 e)) fun n => ?_
    by_cases hn : (n : ℤ) = e
    · rw [← hn, zpow_natCast]
      exact mul_lt_mul_of_pos_right (hde n hn) (pow_pos hρ0 n)
    · rcases (h0 n).eq_or_lt with hc | hc
      · have : d n = 0 := le_antisymm (hc ▸ hdc n) (hd0 n)
        rw [this, zero_mul]
        exact mul_pos hC (zpow_pos hρ0 e)
      · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hdc n) (pow_nonneg hρ0.le n))
          (mono_lt hρ₁ hρ.1 hρ.2 hc hn (hb ρ₁ ⟨le_rfl, h12.le⟩ n) (hb ρ₂ ⟨h12.le, le_rfl⟩ n))
  set ρm := (ρ₁ + ρ₂) / 2 with hρm
  have hm : ρm ∈ Set.Ioo ρ₁ ρ₂ := ⟨by rw [hρm]; linarith, by rw [hρm]; linarith⟩
  have hex : ∃ m : ℕ, (m : ℤ) = e ∧ c m = C := by
    by_contra hno
    push_neg at hno
    have hle : ∀ n : ℕ, (n : ℤ) = e → c n ≤ C := by
      intro n hn
      have := hb ρ₁ ⟨le_rfl, h12.le⟩ n
      rw [← hn, zpow_natCast] at this
      exact le_of_mul_le_mul_right this (pow_pos hρ₁ n)
    have := B ρm hm c h0 (fun _ => le_rfl) fun n hn => lt_of_le_of_ne (hle n hn) (hno n hn)
    rw [hs ρm (Set.Ioo_subset_Icc_self hm)] at this
    exact lt_irrefl _ this
  obtain ⟨m, hme, hcm⟩ := hex
  refine ⟨m, hme, hcm, fun ρ hρ d hd0 hdc hdm => B ρ hρ d hd0 hdc fun n hn => ?_⟩
  have : n = m := by omega
  subst this
  rw [hdm]
  exact hC

end Lead

open GlobalTheory.GaussSlope in

theorem lead_target : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (c ρ₁ ρ₂ : ℝ) (k : ℤ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ < ρ₂ →
    ρ₂ < 1 → 0 < c → (∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ x = c * ρ ^ k) → ∃ (y : Formalism.Per.Fl l) (j : ℕ), 0 ≤ k + j ∧
    ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c ∧ ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, gC l ρ ((l : Formalism.Per.Acris l) ^ j * x -
    (l : Formalism.Per.Acris l) ^ (k + j).toNat * tc l y) < ρ ^ j * gC l ρ x := by
  intro l _ x c ρ₁ ρ₂ k hl1 h12 h21 hc hx
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ₁ : 0 < ρ₁ := lt_of_lt_of_le (by positivity) hl1
  have hG : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, IsGauss l ρ (gC l ρ) := fun ρ hρ =>
    isGauss_gC_target l ρ (hl1.trans hρ.1) (hρ.2.trans_lt h21)
  have hGl : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ (l : Formalism.Per.Acris l) = ρ := by
    intro ρ hρ
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, (hG ρ hρ).2.2.2.2, gA,
      gauss_l l (hρ₁.le.trans hρ.1)]
  have hpm : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ∀ (n : ℕ) (w : Formalism.Per.Acris l),
      gC l ρ ((l : Formalism.Per.Acris l) ^ n * w) = ρ ^ n * gC l ρ w := by
    intro ρ hρ n w
    rw [map_pow_mul _ (hG ρ hρ).2.2.2.1, hGl ρ hρ]
  have hkb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ρ₁ ^ k.toNat ≤ ρ ^ k := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁.trans_le hρ.1
    rcases k with n | n
    · rw [Int.ofNat_eq_coe, Int.toNat_natCast, zpow_natCast]
      exact pow_le_pow_left₀ hρ₁.le hρ.1 n
    · rw [Int.toNat_negSucc, pow_zero, zpow_negSucc]
      exact (one_le_inv₀ (pow_pos hρ0 _)).2 (pow_le_one₀ hρ0.le (hρ.2.trans h21.le))
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (mul_pos hc (pow_pos hρ₁ k.toNat)) h21
  have hrb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ρ ^ r < c * ρ ^ k := fun ρ hρ =>
    calc ρ ^ r ≤ ρ₂ ^ r := pow_le_pow_left₀ (hρ₁.le.trans hρ.1) hρ.2 r
      _ < c * ρ₁ ^ k.toNat := hr
      _ ≤ c * ρ ^ k := mul_le_mul_of_nonneg_left (hkb ρ hρ) hc.le
  obtain ⟨s, z, hxz⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
  obtain ⟨j, a, ha⟩ := exists_pow_mul_eq l s
  have hjx : (l : Formalism.Per.Acris l) ^ j * x =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a + (l : Formalism.Per.Acris l) ^ (j + r) * z := by
    rw [hxz, mul_add, ha, pow_add, mul_assoc]
  have hzb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ ((l : Formalism.Per.Acris l) ^ (j + r) * z) < ρ ^ j * (c * ρ ^ k) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁.trans_le hρ.1
    rw [hpm ρ hρ, pow_add, mul_assoc]
    refine mul_lt_mul_of_pos_left ?_ (pow_pos hρ0 j)
    exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg hρ0.le r) ((hG ρ hρ).1 z).2) (hrb ρ hρ)
  set cc : ℕ → ℝ := fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) with hcc
  have hAn : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, (⨆ n, cc n * ρ ^ n) = c * ρ ^ (k + j) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁.trans_le hρ.1
    obtain ⟨e1, e2, e3, e4, e5⟩ := hG ρ hρ
    have h3 : algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a =
        (l : Formalism.Per.Acris l) ^ j * x + -((l : Formalism.Per.Acris l) ^ (j + r) * z) := by rw [hjx]; ring
    have h4 : gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = ρ ^ j * (c * ρ ^ k) := by
      rw [h3, add_eq_of_lt _ e2 e3 (by rw [e3, hpm ρ hρ j x, hx ρ hρ]; exact hzb ρ hρ), hpm ρ hρ, hx ρ hρ]
    rw [e5, gA] at h4
    rw [h4, zpow_add₀ hρ0.ne', zpow_natCast]
    ring
  have hc1 : ∀ n, cc n ≤ 1 := fun n =>
    Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)
  obtain ⟨m, hme, hcm, hlt⟩ := Lead.lead cc (fun n => by positivity) hc1 hρ₁ h12 h21 hc hAn
  have hmt : (k + j).toNat = m := by omega
  set y := (iterateFrobeniusEquiv (Formalism.Per.Fl l) l m).symm (a.coeff m) with hy
  have hym : y ^ l ^ m = a.coeff m := by
    rw [← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, hy, RingEquiv.apply_symm_apply]
  have hnorm : ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c := by
    rw [← hcm, hcc]
    simp only
    rw [← hym, map_pow]
    push_cast
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    have : ((l ^ m : ℕ) : ℝ) * (1 / (l : ℝ) ^ m) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  let b : Formalism.Per.Ainf l := WittVector.mk l fun n => if n = m then 0 else a.coeff n
  have hbc : ∀ n, b.coeff n = if n = m then 0 else a.coeff n := fun n => rfl
  have hab : a = b + Formalism.Per.tm y * (l : Formalism.Per.Ainf l) ^ m := by
    ext n
    rw [WittVector.coeff_add_of_disjoint]
    · by_cases hn : n = m
      · subst hn
        rw [hbc, if_pos rfl, zero_add, WittVector.teichmuller_mul_pow_coeff, hym]
      · rw [hbc, if_neg hn, WittVector.teichmuller_mul_pow_coeff_of_ne _ hn, add_zero]
    · intro n'
      by_cases hn : n' = m
      · left
        rw [hbc, if_pos hn]
      · right
        exact WittVector.teichmuller_mul_pow_coeff_of_ne _ hn
  refine ⟨y, j, by omega, hnorm, fun ρ hρ => ?_⟩
  have hρI : ρ ∈ Set.Icc ρ₁ ρ₂ := Set.Ioo_subset_Icc_self hρ
  have hρ0 : 0 < ρ := hρ₁.trans hρ.1
  obtain ⟨e1, e2, e3, e4, e5⟩ := hG ρ hρI
  have hsplit : (l : Formalism.Per.Acris l) ^ j * x - (l : Formalism.Per.Acris l) ^ (k + j).toNat * tc l y
      = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) b + (l : Formalism.Per.Acris l) ^ (j + r) * z := by
    rw [hjx, hmt, tc]
    conv_lhs => rw [hab]
    rw [map_add, map_mul, map_pow, map_natCast]
    ring
  let d : ℕ → ℝ := fun n => if n = m then 0 else cc n
  have hbd : ∀ n, ‖(((b.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) = d n := by
    intro n
    by_cases hn : n = m
    · have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [d, hbc, if_pos hn, untilt_zero, ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this]
    · simp only [d, hbc, if_neg hn, hcc]
  have hbn : gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) b) < ρ ^ j * (c * ρ ^ k) := by
    rw [e5, gA]
    simp_rw [hbd]
    refine lt_of_lt_of_le (hlt ρ hρ d (fun n => ?_) (fun n => ?_) (by simp [d])) (le_of_eq ?_)
    · by_cases hn : n = m
      · simp [d, hn]
      · simp only [d, if_neg hn]
        positivity
    · by_cases hn : n = m
      · simp only [d, if_pos hn]
        positivity
      · simp only [d, if_neg hn, le_refl]
    · rw [zpow_add₀ hρ0.ne', zpow_natCast]
      ring
  rw [hsplit, hx ρ hρI]
  exact lt_of_le_of_lt (e2 _ _) (max_lt hbn (hzb ρ hρI))

end GlobalTheory.PMon.Gauss
