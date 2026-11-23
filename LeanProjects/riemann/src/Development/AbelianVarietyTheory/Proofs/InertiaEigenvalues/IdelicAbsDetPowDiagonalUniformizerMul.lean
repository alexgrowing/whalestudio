import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
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
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
namespace GlobalTheory.CellEvalDet

open Matrix

variable {E : Type} [Field E] [NumberField E]

theorem detPow_eq_rpow {n : ℕ} (x : ℝ) (g : GA E n) :
    GlobalTheory.RSJ.detPow E n x g =
      ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) := by
  have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2
  rw [Real.rpow_def_of_pos hpos, ← GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule]
  simp only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]
  change ‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [mul_comm]

theorem det_diagT {R : Type} [CommRing R] {n : ℕ} (t : Fin n → Rˣ) :
    GeneralLinearGroup.det (GlobalTheory.SmGL.diagT R (Fin n) t) = ∏ i, t i := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, det_diagonal, Units.coe_prod]

def posVal : {r : ℝ // 0 < r} →* ℝ where
  toFun r := r
  map_one' := rfl
  map_mul' _ _ := rfl

theorem qV_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < qV E v :=
  lt_of_le_of_ne (Nat.cast_nonneg _) (GlobalTheory.AdeleScale.qV_ne_zero v).symm

end GlobalTheory.CellEvalDet

open GlobalTheory.CellEvalDet Matrix in

theorem GlobalTheory.CellEvalDet.detPow_tl_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (x : ℝ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n x (GlobalTheory.CellDec.tl n ϖ l * g) =
      (∏ w ∈ l.support, (qV E w : ℝ) ^ (-x * ∑ i, (l w i : ℝ))) * GlobalTheory.RSJ.detPow E n x g := by
  intro E _ _ _ n ϖ hϖ l x g
  rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_eq_rpow x (GlobalTheory.CellDec.tl n ϖ l)]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l) =
      ∏ i, finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun y : Fin n → ℤ => y i) rfl l)) := by
    unfold GlobalTheory.CellDec.tl
    rw [det_finGL, det_diagT, map_prod]
  have hmod : ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l)) : ℝ)) =
      ∏ i, ∏ v ∈ l.support, ((qV E v : ℝ) ^ (l v i))⁻¹ := by
    rw [hdet, map_prod]
    change posVal (∏ i, _) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    change ((GroundTheory.Global.IdeleGroup.ideleModule E _ : ℝ)) = _
    rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support (fun v hv => by
      rw [Finsupp.notMem_support_iff] at hv; simp [hv])]
    simp
  rw [hmod, Finset.prod_comm, ← Real.finset_prod_rpow _ _ (fun v _ =>
    Finset.prod_nonneg fun i _ => inv_nonneg.2 (zpow_nonneg (Nat.cast_nonneg _) _))]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hq := qV_pos (E := E) v
  have e : ∀ i, ((qV E v : ℝ) ^ (l v i))⁻¹ = (qV E v : ℝ) ^ (-(l v i : ℝ)) := fun i => by
    rw [Real.rpow_neg hq.le, Real.rpow_intCast]
  simp_rw [e]
  rw [← Real.rpow_sum_of_pos hq, ← Real.rpow_mul hq.le]
  congr 1
  rw [Finset.sum_neg_distrib]
  ring
