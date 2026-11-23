import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

open GlobalTheory.RSJ

namespace GlobalTheory.ZEulProps

theorem norm_prod_le (W W' c₁ c₂ c₃ : ℂ) :
    ‖W * conj W' * c₁ * c₂ * c₃‖ ≤ (‖W * conj W * c₁ * c₂ * c₃‖ + ‖W' * conj W' * c₁ * c₂ * c₃‖) / 2 := by
  simp only [norm_mul, Complex.norm_conj]
  have hK : 0 ≤ ‖c₁‖ * ‖c₂‖ * ‖c₃‖ := by positivity
  nlinarith [mul_nonneg (sq_nonneg (‖W‖ - ‖W'‖)) hK]

theorem psiN_mul_conj {E : Type} [Field E] [NumberField E] {a : ℕ} (u : GA E a) :
    GlobalTheory.JSW.psiN u * conj (GlobalTheory.JSW.psiN u) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [GlobalTheory.JSW.psiN, Circle.norm_coe]

theorem lastRow_unip {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} {u : GA E (m + 1)}
    (hu : u ∈ GlobalTheory.CellDec.NA E (m + 1)) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g := by
  have h := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  refine GlobalTheory.ZUnf.lastRow_mul_of_row fun l => ?_
  by_cases hl : l = Fin.last m
  · subst hl; rw [h.2, Matrix.one_apply_eq]
  · have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
    rw [h.1 _ _ hlt, Matrix.one_apply_ne (Ne.symm hl)]

theorem detPow_unip {E : Type} [Field E] [NumberField E] {a : ℕ} {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) (x : ℝ) :
    GlobalTheory.RSJ.detPow E a x u = 1 := by
  have hd : Matrix.GeneralLinearGroup.det u = 1 := Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu)
  unfold GlobalTheory.RSJ.detPow chiDet
  rw [MonoidHom.comp_apply, hd, map_one]
  simp

end GlobalTheory.ZEulProps

theorem GlobalTheory.ZEulProps.uInt_props : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (φ φ' : GA E (m + 1) → ℂ)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous Φ → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    Measurable (GlobalTheory.ZEul.uInt φ φ' Φ N x) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, GlobalTheory.ZEul.uInt φ φ' Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ' Φ N x g) ∧
    ∀ g, ‖GlobalTheory.ZEul.uInt φ φ' Φ N x g‖ ≤ (‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ + ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖) / 2 := by
  intro E _ _ _ m φ φ' Φ N x hW hW' hl hl' hΦ _
  refine ⟨?_, fun u hu g => ?_, fun g => ?_⟩
  · exact GlobalTheory.ZUnfTheta.measurable_integrand hW.measurable hW'.measurable hΦ N x
  · have hu' : u ∈ GlobalTheory.JSW.NA E (m + 1) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    unfold GlobalTheory.ZEul.uInt
    rw [GlobalTheory.ZEulProps.lastRow_unip hu g, mul_assoc u g, hl u hu', hl' u hu', GlobalTheory.RSJ.Model.detPow_mul,
      GlobalTheory.ZEulProps.detPow_unip hu x, one_mul, map_mul]
    have h1 := GlobalTheory.ZEulProps.psiN_mul_conj u
    linear_combination (GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
      conj (GlobalTheory.JSW.whit φ' (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
      Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) *
      (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ)) * h1
  · unfold GlobalTheory.ZEul.uInt
    exact GlobalTheory.ZEulProps.norm_prod_le _ _ _ _ _
