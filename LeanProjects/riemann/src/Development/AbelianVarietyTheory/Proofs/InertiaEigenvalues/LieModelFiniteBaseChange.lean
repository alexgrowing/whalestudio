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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMoments
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.ThetaSqLow

section Bound

open Matrix GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors Classical

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem norm_mul_pow_le {G : (Fin a → Ad E) → ℂ} (hG : G ∈ schwartzBruhatPi E (Fin a)) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖G y‖ * (1 + ‖fun i => pInf E (y i)‖) ^ M ≤ K := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
    set ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (toMixedPi E a) φ with hψ
    set K₀ : ℝ := 2 ^ M * (Finset.Iic (M, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ with hK₀
    have hK : 0 ≤ K₀ := by positivity
    refine ⟨K₀ * |B|, by positivity, fun y => ?_⟩
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, 0)) (k := M) (n := 0) le_rfl le_rfl ψ
      (fun i => pInf E (y i))
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 : ψ (fun i => pInf E (y i)) = φ (infPartPi y) := by
      rw [hψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, toMixedPi_pInf]
    rw [h2] at h1
    simp only [schwartzBruhatTensorPi, norm_mul]
    calc _ = ((1 + ‖fun i => pInf E (y i)‖) ^ M * ‖φ (infPartPi y)‖) * ‖g (finPartPi y)‖ := by ring
      _ ≤ _ := mul_le_mul h1 ((hB _).trans (le_abs_self _)) (norm_nonneg _) hK
  | zero => exact ⟨0, le_rfl, fun y => by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨K₁, h₁, hG⟩ := hG
    obtain ⟨K₂, h₂, hH⟩ := hH
    refine ⟨K₁ + K₂, by positivity, fun y => le_trans ?_ (add_le_add (hG y) (hH y))⟩
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  | smul c G _ hG =>
    obtain ⟨K, h, hG⟩ := hG
    refine ⟨‖c‖ * K, by positivity, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hG y) (norm_nonneg _)

theorem exists_latt {G : (Fin a → Ad E) → ℂ} (hG : G ∈ schwartzBruhatPi E (Fin a)) :
    ∃ J : (FractionalIdeal (𝓞 E)⁰ E)ˣ, ∀ y, (fun i => pFin E (y i)) ∉ latt a J → G y = 0 := by
  obtain ⟨⟨L, hL, hs⟩, -⟩ := GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments E a G hG
  obtain ⟨J, hJ⟩ := exists_subset_idealFiniteAdeles
    (isCompact_iUnion fun i : Fin a => hL.image (continuous_apply i))
  refine ⟨J, fun y hy => by_contra fun h => hy fun i => hJ (Set.mem_iUnion.2 ⟨i, _, hs y h, rfl⟩)⟩

theorem exists_bound {π' : CuspSub E a} (hπ : π'.IsUnitary) {φ' : GA E a → ℂ} (hφ : φ' ∈ GlobalTheory.JSW.mspanR π')
    {G : (Fin a → Ad E) → ℂ} (hG : G ∈ schwartzBruhatPi E (Fin a)) :
    ∃ C : ℝ, ∀ g : GA E a, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) ≤
        ENNReal.ofReal (C * (GlobalTheory.RSnm.detAbs g)⁻¹) := by
  obtain ⟨J, hJ⟩ := exists_latt hG
  obtain ⟨M, C₁, h₁⟩ := GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest E a J (a * Module.finrank ℚ E)
    GlobalTheory.RSTheta.finrank_pi_Cinf.le
  obtain ⟨K, hK, hGK⟩ := norm_mul_pow_le hG M
  obtain ⟨ψ, rfl, -, -, B, hB⟩ := GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π' hπ φ' hφ
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a π' hπ ψ (Or.inr hφ) [] (latt a J) (GlobalTheory.RSTheta.isCompact_latt J) {1}
    isCompact_singleton 1
  refine ⟨C₁ * (K * |B| * |C₂|), fun g => ?_⟩
  have hδ := GlobalTheory.RSnm.detAbs_pos g
  obtain ⟨hs, hle⟩ := h₁ g (K * |B| * |C₂| * (GlobalTheory.RSnm.detAbs g)⁻¹)
    (fun ξ => ψ.1 g ^ 2 * G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ j)) g.val)) (by positivity)
    (fun ξ hξ => mul_eq_zero_of_right _ (hJ _ hξ))
    (fun ξ ξ' h0 hξ' => by
      have h3 := h₂ g 1 rfl ξ' h0 hξ'
      simp only [GlobalTheory.GLFin.word, mul_one, pow_one] at h3
      set r := ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E)
      have hr : 0 ≤ r := by positivity
      have h4 : ‖ψ.1 g‖ ≤ |C₂| * (r / GlobalTheory.RSnm.detAbs g) :=
        le_trans h3 (mul_le_mul_of_nonneg_right (le_abs_self _) (div_nonneg hr hδ.le))
      rw [norm_mul, norm_pow, mul_assoc, sq]
      calc _ ≤ (|B| * (|C₂| * (r / GlobalTheory.RSnm.detAbs g))) * K :=
            mul_le_mul (mul_le_mul ((hB g).trans (le_abs_self _)) h4 (norm_nonneg _) (abs_nonneg _)) (hGK _)
              (by positivity) (by positivity)
        _ = _ := by ring)
  rw [← ENNReal.tsum_mul_left, mul_assoc C₁]
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hle)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
  refine tsum_congr fun ξ => ?_
  rw [ofReal_norm, enorm_mul, enorm_pow]

end Bound

theorem lintegral_low_ne_top : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ, 1 < x →
      ∫⁻ g in 𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ φ' hφ G hG μ _ 𝓕 h𝓕 x hx
  obtain ⟨C, hC⟩ := exists_bound hπ hφ hG
  have hi : IntegrableOn (fun g : GA E (m + 1) => GlobalTheory.RSnm.detAbs g ^ (x - 1))
      (𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}) μ := GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain E (m + 1) m.succ_pos μ 𝓕 h𝓕 (x - 1) (by linarith)
  refine ne_top_of_le_ne_top (hi.const_mul C).2.ne (lintegral_mono fun g => ?_)
  have hδ := GlobalTheory.RSnm.detAbs_pos g
  refine (mul_le_mul_left (hC g) _).trans ?_
  rw [mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (le_abs_self _))
  beta_reduce
  rw [Real.rpow_sub_one hδ.ne']
  ring

end GlobalTheory.ThetaSqLow
