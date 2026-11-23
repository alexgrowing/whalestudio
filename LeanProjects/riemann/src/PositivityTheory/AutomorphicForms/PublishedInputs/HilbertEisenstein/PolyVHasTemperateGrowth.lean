import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

noncomputable section

open NumberField
open scoped SchwartzMap ContDiff

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def curryE : (Fin 2 → UpperTheory.V.TR.Rinf F) ≃ₗ[ℝ] (Fin 2 × InfinitePlace F → ℝ) where
  toFun y p := y p.1 p.2
  invFun z i v := z (i, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def euclE : (Fin 2 → UpperTheory.V.TR.Rinf F) ≃L[ℝ] EuclideanSpace ℝ (Fin 2 × InfinitePlace F) :=
  (curryE F).toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 2 × InfinitePlace F) ℝ).symm

omit [IsTotallyReal F] in
theorem norm_euclE_sq (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    ‖euclE F y‖ ^ 2 = ∑ v, ((y 0 v) ^ 2 + (y 1 v) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
    ← Finset.sum_add_distrib]
  rfl

def gaussV : 𝓢(Fin 2 → UpperTheory.V.TR.Rinf F, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclE F) (GroundTheory.Global.gaussianSchwartz _)

theorem gaussV_apply (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    gaussV F y = Complex.exp (-(Real.pi : ℂ) * ∑ v, (((y 0 v : ℝ) : ℂ) ^ 2 + ((y 1 v : ℝ) : ℂ) ^ 2)) := by
  simp only [gaussV, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, norm_euclE_sq]
  push_cast
  rfl

def coordV (i : Fin 2) (v : InfinitePlace F) : (Fin 2 → UpperTheory.V.TR.Rinf F) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace F => ℝ) v).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => UpperTheory.V.TR.Rinf F) i)

def linV (v : InfinitePlace F) : (Fin 2 → UpperTheory.V.TR.Rinf F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (coordV F 0 v) + Complex.I • Complex.ofRealCLM.comp (coordV F 1 v)

theorem linV_apply (v : InfinitePlace F) (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    linV F v y = ((y 0 v : ℝ) : ℂ) + Complex.I * ((y 1 v : ℝ) : ℂ) := by
  simp [linV, coordV]

def polyV (y : Fin 2 → UpperTheory.V.TR.Rinf F) : ℂ := ∏ v, linV F v y

theorem polyV_hasTemperateGrowth : (polyV F).HasTemperateGrowth := by
  classical
  have h : ∀ s : Finset (InfinitePlace F),
      (fun y : Fin 2 → UpperTheory.V.TR.Rinf F => ∏ v ∈ s, linV F v y).HasTemperateGrowth := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact Function.HasTemperateGrowth.const (E := Fin 2 → UpperTheory.V.TR.Rinf F) (1 : ℂ)
    | insert a s ha ih =>
      have e : (fun y : Fin 2 → UpperTheory.V.TR.Rinf F => ∏ v ∈ insert a s, linV F v y) =
          (fun y => linV F a y) * (fun y => ∏ v ∈ s, linV F v y) := by
        funext y
        rw [Finset.prod_insert ha]
        rfl
      rw [e]
      exact (linV F a).hasTemperateGrowth.mul ih
  exact h Finset.univ

def archS : 𝓢(Fin 2 → UpperTheory.V.TR.Rinf F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (polyV F) (gaussV F)

theorem archS_apply (y : Fin 2 → UpperTheory.V.TR.Rinf F) : archS F y = arch (y 0) (y 1) := by
  rw [archS, SchwartzMap.smulLeftCLM_apply_apply (polyV_hasTemperateGrowth F), gaussV_apply,
    smul_eq_mul, polyV, arch, Finset.prod_mul_distrib, Finset.mul_sum, Complex.exp_sum]
  simp only [linV_apply]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
