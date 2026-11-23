import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupPowEqPowISupNonnegStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomialStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem untilt_zero' : (0 : Formalism.Per.Fl l).untilt = 0 := by
  rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

theorem isGauss_gC {ρ : ℝ} (h1 : (l : ℝ)⁻¹ ≤ ρ) (h2 : ρ < 1) : IsGauss l ρ (gC l ρ) := by
  have h : ∃ N, IsGauss l ρ N := by
    obtain ⟨N, hN⟩ := GlobalTheory.GaussExt.exists_gauss_acris l ρ h1 h2
    exact ⟨N, hN⟩
  have hfun : gC l ρ = Classical.choose h := by
    funext x
    unfold gC
    rw [dif_pos h]
  rw [hfun]
  exact Classical.choose_spec h

theorem gC_sub_le {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (x y : Formalism.Per.Acris l) :
    gC l ρ (x - y) ≤ max (gC l ρ x) (gC l ρ y) := by
  rw [sub_eq_add_neg]
  calc _ ≤ max (gC l ρ x) (gC l ρ (-y)) := hG.2.1 _ _
    _ = _ := by rw [hG.2.2.1]

theorem gC_pow {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (h1 : gC l ρ 1 = 1) (x : Formalism.Per.Acris l) (n : ℕ) :
    gC l ρ (x ^ n) = gC l ρ x ^ n := by
  induction n with
  | zero => simp [h1]
  | succ n ih => rw [pow_succ, hG.2.2.2.1, ih, pow_succ]

theorem gA_le_of_coeff_zero {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l)
    (ha : a.coeff 0 = 0) : gA l ρ a ≤ ρ := by
  unfold gA
  apply ciSup_le
  intro n
  rcases n with _ | n
  · simpa [ha, untilt_zero'] using h0
  · have hn : ‖(((a.coeff (n + 1)).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ (n + 1)) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one _) (by positivity)
    calc _ ≤ 1 * ρ ^ (n + 1) := mul_le_mul_of_nonneg_right hn (pow_nonneg h0 _)
      _ ≤ ρ := by rw [one_mul]; exact pow_le_of_le_one h0 h1 (Nat.succ_ne_zero n)

theorem tc_mul (a b : Formalism.Per.Fl l) : tc l (a * b) = tc l a * tc l b := by
  unfold tc
  rw [Formalism.Per.tm, map_mul, map_mul]

end GlobalTheory.GaussCancel

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem equal_gauss_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 →
    (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') →
    ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧
      gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  intro l _ w w' hw' heq
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  obtain ⟨⟨c, k, ρ₂, hc, hρ₂, hρ₂1, hm'⟩, -⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l w' hw' (l : ℝ)⁻¹ le_rfl hlinv
  have hm : ∀ ρ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂, gC l ρ w = c * ρ ^ k := fun ρ hρ => by
    rw [heq ρ hρ.1 (lt_of_le_of_lt hρ.2 hρ₂1)]; exact hm' ρ hρ
  obtain ⟨y', j', hkj', hy', hL'⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w' c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm'
  obtain ⟨y, j, hkj, hy, hL⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm

  have hy'0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy'
    linarith
  have hdvd : y' ∣ y := by
    apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
    have hq : ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
      rw [GlobalTheory.RingBasics.mem_OC, norm_div, hy, hy', div_self hc.ne']
    refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
    change ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) *
      (((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]))
    field_simp
  obtain ⟨u, hu⟩ := hdvd
  have hu1 : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((1 : Formalism.Per.Fl l).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
    have h := hy
    rw [hu, map_mul] at h
    push_cast at h
    rw [norm_mul, hy'] at h
    rw [map_one]
    simp only [OneMemClass.coe_one, norm_one]
    have : c * ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c * 1 := by rw [h, mul_one]
    exact mul_left_cancel₀ hc.ne' this
  obtain ⟨ζ, o, ho, hζ, hζ0, hlt⟩ := GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio l u 1 one_ne_zero hu1
  rw [mul_one, map_one] at hlt
  simp only [OneMemClass.coe_one, norm_one] at hlt

  set ρ₀ : ℝ := ((l : ℝ)⁻¹ + ρ₂) / 2 with hρ₀def
  have hρ₀a : (l : ℝ)⁻¹ < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₀b : ρ₀ < ρ₂ := by rw [hρ₀def]; linarith
  have hρ₀1 : ρ₀ < 1 := lt_trans hρ₀b hρ₂1
  have hρ₀pos : 0 < ρ₀ := lt_trans hlpos hρ₀a
  have hIoo : ρ₀ ∈ Set.Ioo (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a, hρ₀b⟩
  have hIcc : ρ₀ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a.le, hρ₀b.le⟩
  refine ⟨ζ, o, ρ₀, ho, hζ, hζ0, hρ₀a, hρ₀1, ?_⟩
  have hG := isGauss_gC (l := l) hρ₀a.le hρ₀1
  obtain ⟨hb1, hbl, -, hbt, -⟩ := GlobalTheory.T.gaussNormAcris_basic_values l ρ₀ hρ₀a.le hρ₀1
  have hlpow : ∀ n : ℕ, gC l ρ₀ ((l : Formalism.Per.Acris l) ^ n) = ρ₀ ^ n := fun n => by
    rw [gC_pow hG hb1, hbl]
  have hGw' : gC l ρ₀ w' = c * ρ₀ ^ k := hm' ρ₀ hIcc
  have hGw : gC l ρ₀ w = c * ρ₀ ^ k := hm ρ₀ hIcc
  set T : ℝ := ρ₀ ^ (max j j') * (c * ρ₀ ^ k) with hTdef
  set J : ℕ := max j j' with hJ
  set m : ℕ := (k + J).toNat with hmdef

  have hA : ∀ (x : Formalism.Per.Acris l) (z : Formalism.Per.Fl l) (i : ℕ), 0 ≤ k + i → i ≤ J → gC l ρ₀ x = c * ρ₀ ^ k →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ i * x - (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) < ρ₀ ^ i * gC l ρ₀ x →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z) < T := by
    intro x z i hki hiJ hx hlt'
    have hmi : m = (J - i) + (k + i).toNat := by rw [hmdef]; omega
    have heqA : (l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z =
        (l : Formalism.Per.Acris l) ^ (J - i) * ((l : Formalism.Per.Acris l) ^ i * x -
          (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) := by
      have e : (l : Formalism.Per.Acris l) ^ J = (l : Formalism.Per.Acris l) ^ (J - i) * (l : Formalism.Per.Acris l) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hiJ]
      rw [hmi, e, pow_add]
      ring
    rw [heqA, hG.2.2.2.1, hlpow, hTdef, ← hx]
    calc ρ₀ ^ (J - i) * gC l ρ₀ _ < ρ₀ ^ (J - i) * (ρ₀ ^ i * gC l ρ₀ x) :=
          mul_lt_mul_of_pos_left hlt' (pow_pos hρ₀pos _)
      _ = ρ₀ ^ J * gC l ρ₀ x := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hiJ]
  have hAw := hA w y j hkj (le_max_left _ _) hGw (hL ρ₀ hIoo)
  have hAw' := hA w' y' j' hkj' (le_max_right _ _) hGw' (hL' ρ₀ hIoo)

  have hζ1 : gC l ρ₀ (tc l ζ) ≤ 1 := (hG.1 _).2
  have hdiff : gC l ρ₀ (tc l u - tc l ζ) < 1 := by
    have hsplit : tc l u - tc l ζ = tc l (u - ζ) + algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)
        (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) := by
      unfold tc
      rw [map_sub, map_sub]
      ring
    have hc0 : (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)).coeff 0 = 0 := by
      change WittVector.constantCoeff (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) = 0
      rw [map_sub, map_sub]
      change (Formalism.Per.tm u).coeff 0 - (Formalism.Per.tm ζ).coeff 0 - (Formalism.Per.tm (u - ζ)).coeff 0 = 0
      simp [Formalism.Per.tm, WittVector.teichmuller_coeff_zero]
    rw [hsplit]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt ?_ ?_)
    · rw [hbt]; exact hlt
    · rw [hG.2.2.2.2]
      exact lt_of_le_of_lt (gA_le_of_coeff_zero hρ₀pos.le hρ₀1.le _ hc0) hρ₀1
  have hmz : ((m : ℕ) : ℤ) = k + J := by rw [hmdef]; exact Int.toNat_of_nonneg (by omega)
  have hD : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y')) < T := by
    have : tc l y - tc l ζ * tc l y' = tc l y' * (tc l u - tc l ζ) := by
      rw [hu, tc_mul]; ring
    rw [this, hG.2.2.2.1, hG.2.2.2.1, hlpow, hbt, hy']
    have hT : ρ₀ ^ m * c = T := by
      rw [hTdef, ← zpow_natCast, hmz, zpow_add₀ hρ₀pos.ne', zpow_natCast]
      ring
    rw [← hT, ← mul_assoc]
    exact mul_lt_of_lt_one_right (mul_pos (pow_pos hρ₀pos _) hc) hdiff
  have hB : gC l ρ₀ (tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y')) < T := by
    rw [hG.2.2.2.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (hG.1 _).1 hζ1) hAw'
  have hid : (l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w') =
      ((l : Formalism.Per.Acris l) ^ J * w - (l : Formalism.Per.Acris l) ^ m * tc l y) -
        tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y') +
        (l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y') := by ring
  have hbig : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w')) < T := by
    rw [hid]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt (lt_of_le_of_lt (gC_sub_le hG _ _) (max_lt hAw hB)) ?_)
    exact hD
  rw [hG.2.2.2.1, hlpow, hTdef, ← hGw'] at hbig
  exact lt_of_mul_lt_mul_left hbig (pow_nonneg hρ₀pos.le _)

end GlobalTheory.GaussCancel
