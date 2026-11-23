import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
import ReciprocityTheory.SemistableReduction.ShareDetA
open Filter Topology Matrix
open scoped ContDiff

namespace GlobalTheory

theorem metric_pullback_contDiffOn : ∀ (d : ℕ) (U U' : Set (ReciprocityTheory.L2DbarEstimates.V d)) (τ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (b b' : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ), IsOpen U → DifferentiableOn ℂ τ U → Set.MapsTo τ U U' → (∀ k l, ContDiffOn ℝ ∞ (fun v => b' v k l) U') → (∀ v ∈ U, ∀ ξ ζ : ReciprocityTheory.L2DbarEstimates.V d, (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp = ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp) → ∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U := by
  intro d U U' τ b b' hU hτ hmap hb' hpull k l
  have han : AnalyticOnNhd ℂ τ U := by
    have hc : ∀ i, AnalyticOnNhd ℂ (fun v => (τ v).ofLp i) U := fun i =>
      ReciprocityTheory.MultiplicativeHeights.analyticOnNhd_V_of_differentiableOn hU
        ((EuclideanSpace.proj i : ReciprocityTheory.L2DbarEstimates.V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hτ)
    intro v hv
    let e := EuclideanSpace.equiv (Fin d) ℂ
    have h : AnalyticAt ℂ (fun w => e (τ w)) v :=
      analyticAt_pi_iff.mpr fun i => by simpa [e] using hc i v hv
    have h2 : AnalyticAt ℂ (fun w => e.symm (e (τ w))) v :=
      ((e.symm : (Fin d → ℂ) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V d).analyticAt (e (τ v))).comp (f := fun w => e (τ w)) h
    simpa using h2
  have hD : ∀ (w : ReciprocityTheory.L2DbarEstimates.V d) (i : Fin d),
      ContDiffOn ℝ ∞ (fun v => (fderiv ℂ τ v w).ofLp i) U := by
    intro w i
    have h1 : AnalyticOnNhd ℂ (fun v => fderiv ℂ τ v) U := han.fderiv
    have h2 : AnalyticOnNhd ℂ (fun v => (fderiv ℂ τ v w).ofLp i) U := by
      intro v hv
      exact (((EuclideanSpace.proj i : ReciprocityTheory.L2DbarEstimates.V d →L[ℂ] ℂ).comp
        (ContinuousLinearMap.apply ℂ (ReciprocityTheory.L2DbarEstimates.V d) w)).analyticAt _).comp (h1 v hv)
    exact (h2.contDiffOn (n := ∞) hU.uniqueDiffOn).restrict_scalars ℝ
  have hτR : ContDiffOn ℝ ∞ τ U := (han.contDiffOn (n := ∞) hU.uniqueDiffOn).restrict_scalars ℝ
  have hB : ∀ i j, ContDiffOn ℝ ∞ (fun v => b' (τ v) i j) U :=
    fun i j => (hb' i j).comp hτR hmap
  have key : ∀ v ∈ U, b v k l = ∑ j, (∑ i, (fderiv ℂ τ v (EuclideanSpace.single k 1)).ofLp i
      * b' (τ v) i j) * star ((fderiv ℂ τ v (EuclideanSpace.single l 1)).ofLp j) := by
    intro v hv
    have h := hpull v hv (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)
    simp only [dotProduct, vecMul, Pi.star_apply] at h
    rw [← h]
    simp [Pi.single_apply]
  refine ContDiffOn.congr ?_ key
  refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ ?_
  · exact ContDiffOn.sum fun i _ => (hD _ i).mul (hB i j)
  · exact (Complex.conjCLE.contDiff.comp_contDiffOn (hD (EuclideanSpace.single l 1) j)).congr (fun x _ => by simp [Complex.conjCLE_apply, Complex.star_def])

end GlobalTheory
