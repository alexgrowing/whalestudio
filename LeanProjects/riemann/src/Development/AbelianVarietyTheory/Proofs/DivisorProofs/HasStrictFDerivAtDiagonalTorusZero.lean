import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

theorem hasStrictFDerivAt_torus_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => fun τ a b => (mat x τ * diagonal (fun c => Complex.exp (Complex.I * (angles (θ τ) c : ℂ))) * (mat x τ)⁻¹) a b) (torusDer x) 0 := by
  refine hasStrictFDerivAt_pi'' fun τ => hasStrictFDerivAt_pi'' fun a => hasStrictFDerivAt_pi'' fun b => ?_
  set A : Fin r → ((Ψ → Fin (r - 1) → ℝ) →L[ℝ] ℂ) := fun c =>
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj c).comp ((LinearMap.toContinuousLinearMap (anglesL r)).comp (ContinuousLinearMap.proj τ))) with hA
  have hAapp : ∀ c θ, A c θ = (angles (θ τ) c : ℂ) := fun c θ => rfl
  have hc : ∀ c : Fin r, HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => mat x τ a c * Complex.exp (Complex.I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ c b)
      (((mat x τ)⁻¹ c b) • (mat x τ a c • (Complex.exp (Complex.I * (angles ((0 : Ψ → Fin (r - 1) → ℝ) τ) c : ℂ)) • (Complex.I • A c)))) 0 := by
    intro c
    have h1 : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => (angles (θ τ) c : ℂ)) (A c) 0 := (A c).hasStrictFDerivAt
    exact ((h1.const_mul Complex.I).cexp.const_mul (mat x τ a c)).mul_const ((mat x τ)⁻¹ c b)
  have hs := HasStrictFDerivAt.sum (u := Finset.univ) (fun c _ => hc c)
  refine (hs.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext θ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply, torusDer_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hAapp,
      angles_zero, Pi.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, smul_eq_mul]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · refine Filter.Eventually.of_forall fun θ => ?_
    simp only [Finset.sum_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
end GlobalTheory.TorusFrame
