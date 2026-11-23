import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMoments
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.SBThetaUpper

open GroundTheory.Automorphic.GJMatrix GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GlobalTheory.ShortVecDecay GlobalTheory.RSTheta

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_norm_mul_pow_le {G : (Fin a → Ad E) → ℂ} (hG : G ∈ schwartzBruhatPi E (Fin a)) (M : ℕ) :
    ∃ B : ℝ, ∀ y, ‖G y‖ * (1 + ‖fun i => pInf E (y i)‖) ^ M ≤ B := by
  classical
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi E).mp hg
    obtain ⟨B, hB⟩ := h1.continuous.bounded_above_of_compact_support h2
    set S := (toMixedPi E a).symm
    set C := ‖(S : (Fin a → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin a → Cinf E))‖
    have hC : 0 ≤ C := norm_nonneg _
    obtain ⟨A₀, -, hA₀⟩ := φ.decay 0 0
    obtain ⟨A₁, -, hA₁⟩ := φ.decay M 0
    refine ⟨(1 + C) ^ M * 2 ^ M * (A₀ + A₁) * B, fun y => ?_⟩
    rw [GlobalTheory.SchwartzBruhatMoments.pInfPi_eq, schwartzBruhatTensorPi, norm_mul]
    have hBy := hB (finPartPi y)
    generalize finPartPi y = z at hBy
    generalize infPartPi y = u
    have a0 := hA₀ u
    have a1 := hA₁ u
    rw [norm_iteratedFDeriv_zero] at a0 a1
    rw [pow_zero, one_mul] at a0
    have h1 : ‖S u‖ ≤ C * ‖u‖ := (S : (Fin a → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin a → Cinf E)).le_opNorm u
    have h2 : 1 + ‖S u‖ ≤ (1 + C) * (1 + ‖u‖) := by nlinarith [norm_nonneg u, norm_nonneg (S u)]
    have h3 : (1 + ‖S u‖) ^ M ≤ (1 + C) ^ M * (2 ^ M * (1 + ‖u‖ ^ M)) := by
      calc (1 + ‖S u‖) ^ M ≤ ((1 + C) * (1 + ‖u‖)) ^ M := pow_le_pow_left₀ (by positivity) h2 M
        _ = (1 + C) ^ M * (1 + ‖u‖) ^ M := mul_pow _ _ _
        _ ≤ (1 + C) ^ M * (2 ^ M * (1 + ‖u‖ ^ M)) :=
          mul_le_mul_of_nonneg_left (GlobalTheory.SchwartzBruhatMoments.one_add_pow_le (norm_nonneg u) M) (by positivity)
    have h4 : ‖φ u‖ * (1 + ‖S u‖) ^ M ≤ (1 + C) ^ M * 2 ^ M * (A₀ + A₁) := by
      calc ‖φ u‖ * (1 + ‖S u‖) ^ M ≤ ‖φ u‖ * ((1 + C) ^ M * (2 ^ M * (1 + ‖u‖ ^ M))) :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = ((1 + C) ^ M * 2 ^ M) * (‖φ u‖ + ‖u‖ ^ M * ‖φ u‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add a0 a1) (by positivity)
    calc ‖φ u‖ * ‖g z‖ * (1 + ‖S u‖) ^ M = ‖φ u‖ * (1 + ‖S u‖) ^ M * ‖g z‖ := by ring
      _ ≤ _ := mul_le_mul h4 hBy (norm_nonneg _) (le_trans (by positivity) h4)
  | zero => exact ⟨0, fun y => by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨B₁, h1⟩ := hG
    obtain ⟨B₂, h2⟩ := hH
    refine ⟨B₁ + B₂, fun y => le_trans ?_ (add_le_add (h1 y) (h2 y))⟩
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  | smul c G _ hG =>
    obtain ⟨B, h⟩ := hG
    refine ⟨‖c‖ * B, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem isSmallKernel_sq_mul {φ : GA E a → ℂ} (h : Decays φ) {G : (Fin a → Ad E) → ℂ}
    (hG : G ∈ schwartzBruhatPi E (Fin a)) : IsSmallKernel fun g y => φ g ^ 2 * G y := by
  obtain ⟨L, hL, hs⟩ := (GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments E a G hG).1
  refine ⟨⟨L, hL, fun g y hy => hs y (right_ne_zero_of_mul hy)⟩, fun L hL N M => ?_⟩
  obtain ⟨C, hC⟩ := h L hL {1} isCompact_singleton N
  obtain ⟨C', hC'⟩ := h L hL {1} isCompact_singleton 0
  obtain ⟨B, hB⟩ := exists_norm_mul_pow_le hG M
  refine ⟨|C| * |C'| * |B|, fun g ξ hξ hm y => ?_⟩
  have hΔ : 0 < (GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det g) : ℝ) :=
    (GroundTheory.Global.IdeleGroup.ideleModule E _).2
  have h1 := (hC g 1 rfl ξ hξ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h2 := (hC' g 1 rfl ξ hξ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))
  rw [mul_one] at h1 h2
  have h3 : ‖G y‖ ≤ |B| * (1 + ‖fun i => pInf E (y i)‖) ^ (-(M : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact (hB y).trans (le_abs_self B)
  beta_reduce
  rw [norm_mul, sq, norm_mul]
  refine (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)).trans_eq ?_
  ring

theorem lintegral_theta_upper_ne_top : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ,
      ∫⁻ g in 𝓕 ∩ {g | 1 ≤ GlobalTheory.RSnm.detAbs g}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ' φ' hφ' G hG μ _ 𝓕 h𝓕 x
  have hd : Decays φ' := GlobalTheory.MSpanDecay.Good.decays (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ' hφ')
  obtain ⟨C, hC⟩ := (isSmallKernel_sq_mul hd hG).tsum_le (N := ⌈x⌉₊ + 1) (by omega)
  have hI := ((integrableOn_absDet_rpow_neg (Nat.succ_pos m) μ h𝓕 (s := (⌈x⌉₊ + 1 : ℕ) - x)
      (by push_cast; linarith [Nat.le_ceil x])).const_mul C).lintegral_lt_top
  refine ne_top_of_le_ne_top hI.ne (lintegral_mono fun g => ?_)
  obtain ⟨hs, hle⟩ := hC g
  have h0 := GlobalTheory.RSnm.detAbs_pos g
  change _ ≤ C * GlobalTheory.RSnm.detAbs g ^ _ at hle
  change _ ≤ ENNReal.ofReal (C * GlobalTheory.RSnm.detAbs g ^ _)
  rw [← ENNReal.tsum_mul_left]
  simp only [← enorm_pow, ← enorm_mul]
  simp only [← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs,
    ← ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _), neg_sub, sub_eq_neg_add, Real.rpow_add h0, ← mul_assoc]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (by positivity))

end GlobalTheory.SBThetaUpper
