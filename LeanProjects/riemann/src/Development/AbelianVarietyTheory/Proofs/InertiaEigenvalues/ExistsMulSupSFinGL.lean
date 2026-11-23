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
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E]

open Classical

def idemOff (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E :=
  ⟨fun v => if v ∈ S then 0 else 1, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact zero_mem _
    · simp only [h, if_false]; exact one_mem _⟩

theorem pLoc_idemOff (S : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) :
    pLoc E v (idemOff S) = if v ∈ S then 0 else 1 := rfl

theorem idemOff_mul_self (S : Finset (HeightOneSpectrum (𝓞 E))) : idemOff S * idemOff S = idemOff S :=
  FiniteAdeleRing.ext _ fun v => by
    change pLoc E v (idemOff S) * pLoc E v (idemOff S) = pLoc E v (idemOff S)
    rw [pLoc_idemOff]; split_ifs <;> simp

def cutS (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E →ₙ+* Af E where
  toFun x := idemOff S * x
  map_mul' x y := by
    calc idemOff S * (x * y) = (idemOff S * idemOff S) * (x * y) := by rw [idemOff_mul_self]
      _ = idemOff S * x * (idemOff S * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pLoc_cutS (S : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) (x : Af E) :
    pLoc E v (cutS S x) = (if v ∈ S then 0 else 1) * pLoc E v x := by
  change pLoc E v (idemOff S * x) = _
  rw [map_mul, pLoc_idemOff]

theorem map_pLoc_pFin_finGL {a : ℕ} (v : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a k) = Matrix.GeneralLinearGroup.map (pLoc E v) k := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun x : GL (Fin a) (Af E) => pLoc E v (x i j)) (pFin_finGL k)

theorem exists_mul_supS_finGL : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a),
    g ∈ GlobalTheory.CellDec.C0 E a S →
    ∃ u ∈ GlobalTheory.CellDec.NA E a, ∃ h ∈ GlobalTheory.JSW.supS E a S, ∃ k : GL (Fin a) (Af E),
      (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v a) ∧ (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) ∧
      g = u * h * finGL E a k := by
  intro E _ _ a S g hg
  obtain ⟨u, hu, k₁, hk₁, rfl⟩ := hg
  set k : GL (Fin a) (Af E) := cornerGL a (cutS S) (Matrix.GeneralLinearGroup.map (pFin E) k₁) with hk
  have hkv : ∀ v, v ∉ S → Matrix.GeneralLinearGroup.map (pLoc E v) k =
      Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) k₁ := by
    intro v hv
    rw [hk, map_cornerGL_of_hom _ _ (pLoc E v) (fun x => by rw [pLoc_cutS, if_neg hv, one_mul])]
    exact Units.ext (Matrix.ext fun i j => rfl)
  have hkS : ∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1 := fun v hv =>
    map_cornerGL_of_zero _ _ (fun x => by rw [pLoc_cutS, if_pos hv, zero_mul]) _
  have hK : ∀ v, v ∉ S → Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) k₁ ∈ KGL v a := by
    intro v hv
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hk₁ v) hv
  refine ⟨u, hu, k₁ * (finGL E a k)⁻¹, ?_, k, fun v => ?_, hkS, ?_⟩
  · intro w hw
    rw [map_mul, map_inv, map_pLoc_pFin_finGL, hkv w hw, mul_inv_cancel]
  · by_cases hv : v ∈ S
    · rw [hkS v hv]; exact one_mem _
    · rw [hkv v hv]; exact hK v hv
  · group

end GlobalTheory.CellDec
