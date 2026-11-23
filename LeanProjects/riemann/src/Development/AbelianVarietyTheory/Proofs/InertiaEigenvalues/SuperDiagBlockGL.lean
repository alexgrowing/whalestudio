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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBounded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolic
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
noncomputable section

namespace GlobalTheory.RSnmUnfProps

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

theorem superDiag_blockGL {R : Type} [CommRing R] {j n : ℕ} (hj : j ≤ n) (g : GL (Fin j) R) :
    GlobalTheory.Whittaker.superDiag (blockGL hj g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  simp only [Finset.sum_filter]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
  · intro i hi
    have hij : ¬ (i : ℕ) < j := fun h => hi ⟨⟨i, h⟩, rfl⟩
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · rw [coe_blockGL, blockMat_apply, dif_neg hij, if_neg]
      intro h; rw [h] at hb; omega
    · rfl
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro b hb
      have hbj : ¬ (b : ℕ) < j := fun h => hb ⟨⟨b, h⟩, rfl⟩
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dif_pos (by simp), dif_neg hbj]
      · rfl
    · intro b
      simp only [Fin.coe_castLE]
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dif_pos (by simp), dif_pos (by simp)]
        rfl
      · rfl

variable {E : Type} [Field E] [NumberField E]

theorem psiN_blockGL {j n : ℕ} (hj : j ≤ n) (g : GA E j) :
    GlobalTheory.JSW.psiN (blockGL hj g : GA E n) = GlobalTheory.JSW.psiN g := by
  unfold GlobalTheory.JSW.psiN
  rw [superDiag_blockGL]

theorem norm_psiN {a : ℕ} (u : GA E a) : ‖GlobalTheory.JSW.psiN u‖ = 1 := by
  simp [GlobalTheory.JSW.psiN, Circle.norm_coe]

theorem blockGL_mem_NA {j n : ℕ} (hj : j ≤ n) {u : GA E j} (hu : u ∈ GlobalTheory.JSW.NA E j) :
    (blockGL hj u : GA E n) ∈ GlobalTheory.JSW.NA E n := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb hc
    · exact h1 _ _ (by rw [Fin.lt_def] at hik ⊢; exact hik)
    · rfl
    · exact absurd hik (by rw [hc]; exact lt_irrefl _)
    · rfl
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb
    · exact h2 _
    · rfl
    · exact absurd rfl hb

theorem detAbs_unip {a : ℕ} {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) : GlobalTheory.RSnm.detAbs u = 1 := by
  have hd : Matrix.GeneralLinearGroup.det u = 1 := Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu)
  rw [GlobalTheory.RSnm.detAbs, hd, map_one]; rfl

end GlobalTheory.RSnmUnfProps

open GroundTheory.Automorphic.FourierWhittaker (blockGL) in

theorem GlobalTheory.RSnmUnfProps.uIntNM_props : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (F : (Fin (m + 1) → Ad E) → ℂ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) →
    Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)) ∧
    Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) ∧
    (∀ x : ℝ, Measurable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x)) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (u * g))‖ = ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ∧
      ‖GlobalTheory.JSW.whit φ' (u * g)‖ = ‖GlobalTheory.JSW.whit φ' g‖ ∧
      GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g ∧ GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g ∧
      ∀ x : ℝ, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (u * g) = GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g) ∧
    ∀ (x : ℝ) (g : GA E (m + 1)), ‖GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g‖ ≤
      (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) +
        ‖GlobalTheory.JSW.whit φ' g‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ x) / 2 := by
  intro E _ _ _ m r S φ φ' F hW hW' hl hl' hF
  have hmn : m + 1 ≤ m + r + 1 + 1 := by omega
  have cW : Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (blockGL hmn g)) :=
    hW.comp (GlobalTheory.RSnm.continuous_blockGL hmn)
  have cF : Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) :=
    hF.comp GlobalTheory.ZUnfTheta.continuous_lastRow
  have cD : ∀ y : ℂ, Continuous (fun g : GA E (m + 1) => ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ y) := fun y =>
    (Complex.continuous_ofReal.comp GlobalTheory.RSnm.continuous_detAbs).cpow continuous_const
      fun h => Complex.ofReal_mem_slitPlane.2 (GlobalTheory.RSnm.detAbs_pos h)
  have hwu : ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      GlobalTheory.JSW.whit φ (blockGL hmn (u * g)) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ (blockGL hmn g) := by
    intro u hu g
    have hu' : u ∈ GlobalTheory.JSW.NA E (m + 1) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    rw [map_mul, hl _ (GlobalTheory.RSnmUnfProps.blockGL_mem_NA hmn hu'), GlobalTheory.RSnmUnfProps.psiN_blockGL]
  refine ⟨cW, cF, fun x => ?_, fun u hu g => ?_, fun x g => ?_⟩
  · unfold GlobalTheory.RSnmUnf.uIntNM
    exact (((cW.mul (Complex.continuous_conj.comp hW')).mul cF).mul (cD _)).measurable
  · have hu' : u ∈ GlobalTheory.JSW.NA E (m + 1) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    have hlr := GlobalTheory.ZEulProps.lastRow_unip hu g
    have hd : GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g := by
      rw [GlobalTheory.RSnm.detAbs_mul, GlobalTheory.RSnmUnfProps.detAbs_unip hu, one_mul]
    refine ⟨?_, ?_, hlr, hd, fun x => ?_⟩
    · rw [hwu u hu g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · rw [hl' u hu' g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · unfold GlobalTheory.RSnmUnf.uIntNM
      rw [hwu u hu g, hl' u hu' g, hlr, hd, map_mul]
      have h1 := GlobalTheory.ZEulProps.psiN_mul_conj u
      linear_combination (GlobalTheory.JSW.whit φ (blockGL hmn g) * conj (GlobalTheory.JSW.whit φ' g) *
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g) *
        ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2)) * h1

  · have hdp := GlobalTheory.RSnm.detAbs_pos g
    have hre : ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2).re = (x - ((r : ℝ) + 1)) / 2 + x / 2 := by
      push_cast
      simp only [Complex.sub_re, Complex.div_re, Complex.add_re, Complex.ofReal_re, Complex.natCast_re,
        Complex.one_re, Complex.natCast_im, Complex.one_im, Complex.add_im, Complex.ofReal_im]
      norm_num
      ring
    unfold GlobalTheory.RSnmUnf.uIntNM
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hdp, hre,
      Real.rpow_add hdp]
    have hA : GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) = (GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    have hB : GlobalTheory.RSnm.detAbs g ^ x = (GlobalTheory.RSnm.detAbs g ^ (x / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    rw [hA, hB]
    set a := ‖GlobalTheory.JSW.whit φ (blockGL hmn g)‖
    set b := ‖GlobalTheory.JSW.whit φ' g‖
    set c := ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖
    set α := GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)
    set β := GlobalTheory.RSnm.detAbs g ^ (x / 2)
    have hc : 0 ≤ c := norm_nonneg _
    nlinarith [mul_nonneg hc (sq_nonneg (a * α - b * β))]
