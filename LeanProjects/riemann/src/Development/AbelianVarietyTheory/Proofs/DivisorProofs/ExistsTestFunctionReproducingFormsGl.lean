import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraExistsReproducingTestFunctionGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlphaSmoothingFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingLaplacianPolySolutiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinitStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HCSmoothGL

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem isAddHaarMeasure_volume_Lie : (volume : Measure (Lie E a)).IsAddHaarMeasure := by
  haveI : SigmaFinite (volume : Measure (InfinitePlace E → ℂ)) := inferInstance
  haveI : (volume : Measure (Fin a → InfinitePlace E → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : SigmaFinite (volume : Measure (Fin a → InfinitePlace E → ℂ)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

def conjCL (k : Kinf E a) : Lie E a →L[ℝ] Lie E a := (lmul (toL k.1)).comp (rmul (toL (star k.1)))

theorem conjCL_apply (k : Kinf E a) (x : Lie E a) : conjCL k x = toL (k.1 * Matrix.of x * star k.1) := by
  show toL (k.1 * (Matrix.of x * star k.1)) = _
  rw [mul_assoc]

theorem conjCL_mul (k k' : Kinf E a) (x : Lie E a) : conjCL (k * k') x = conjCL k (conjCL k' x) := by
  rw [conjCL_apply, conjCL_apply, conjCL_apply]
  show toL _ = toL (k.1 * (k'.1 * Matrix.of x * star k'.1) * star k.1)
  simp [mul_assoc, star_mul]

theorem conjCL_one (x : Lie E a) : conjCL 1 x = x := by
  simp [conjCL_apply]

def conjCE (k : Kinf E a) : Lie E a ≃L[ℝ] Lie E a :=
  ContinuousLinearEquiv.equivOfInverse (conjCL k) (conjCL k⁻¹)
    (fun x => by rw [← conjCL_mul, inv_mul_cancel, conjCL_one])
    (fun x => by rw [← conjCL_mul, mul_inv_cancel, conjCL_one])

def dev (x : Lie E a) : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of x - 1

def fdist (x : Lie E a) : ℝ :=
  ∑ w : InfinitePlace E, (Matrix.trace (dev x * Matrix.conjTranspose (dev x)) w).re

variable [IsTotallyComplex E]

def avgChart [MeasurableSpace (Kinf E a)] (ν : Measure (Kinf E a)) (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) : ℂ :=
  ∫ k, chart φ g (conjCL k x) ∂ν

open Classical in

def extL : (GL (Fin a) (Cinf E) → ℂ) →ₗ[ℂ] (Lie E a → ℂ) where
  toFun F x := if h : IsUnit (Matrix.of x) then F h.unit else 0
  map_add' F G := by funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [h]
  map_smul' c F := by funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [h]

theorem exists_smooth_beta : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ β : Lie E a → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ invSet E a ∧ ∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  intro E _ _ _ a L W hW X hX N
  have hν := isAddHaarMeasure_volume_Lie (E := E) (a := a)
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite E a L W hW X hX N
  obtain ⟨α, hα, h⟩ := GlobalTheory.T.exists_testFunction_reproducing_laplacianPoly_solutions E a volume hν p hp0
  refine ⟨α, hα.1, hα.2.1, hα.2.2, fun φ hφm x => ?_⟩
  have hφ := hp φ hφm
  have h1 := h (chart φ.1 x) (φ.2 x) (fun y hy => by
    rw [Polynomial.aeval_eq_sum_range] at hφ
    have e := congrArg (fun ψ : Sm E a => chart ψ.1 x y) hφ
    rw [LinearMap.sum_apply] at e
    simp only [LinearMap.smul_apply] at e
    rw [GlobalTheory.HCFiniteSm.chart_sum' _ _ (fun k => (GlobalTheory.HCAlpha.lapOp E a ^ k) φ) _ hy] at e
    have e0 : chart (0 : Sm E a).1 x y = 0 := by simp [chart]
    rw [e0] at e
    rw [← e, GlobalTheory.HCAlpha.polyF, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.HCAlpha.chart_lapOp_pow E a φ x k y hy])
  simp only [mul_comm (chart φ.1 x _)]
  rw [h1]
  have := chart_val φ.1 x 1
  simpa using this

end GlobalTheory.HCSmoothGL
