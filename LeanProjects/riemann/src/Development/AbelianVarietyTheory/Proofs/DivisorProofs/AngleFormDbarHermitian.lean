import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtDelApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.CurveDens

theorem vec_eq_sum_single_smul {D : ℕ} (ξ : V D) :
    ξ = ∑ j, ξ j • (EuclideanSpace.single j (1 : ℂ) : V D) := by
  ext i
  simp [Pi.single_apply]

theorem angleForm_add_vec {D : ℕ} (n : ℕ) (a a' : V D → ℝ) (q : V D → ℂ) (ξ η z : V D) :
    angleForm n a a' q (ξ + η) z = angleForm n a a' q ξ z + angleForm n a a' q η z := by
  simp only [angleForm, map_add, map_sub, map_mul]
  ring

theorem angleForm_eq_sum_coeff {D : ℕ} (n : ℕ) (a a' : V D → ℝ) (q : V D → ℂ) (ξ z : V D) :
    angleForm n a a' q ξ z = ∑ j, ξ j * angleForm n a a' q (EuclideanSpace.single j 1) z := by
  let L : V D →ₗ[ℂ] ℂ :=
    { toFun := fun η => angleForm n a a' q η z
      map_add' := fun η η' => angleForm_add_vec n a a' q η η' z
      map_smul' := fun c η => (angleForm_props _ n a a' q η z).1 c }
  change L ξ = ∑ j, ξ j * L (EuclideanSpace.single j 1)
  conv_lhs => rw [vec_eq_sum_single_smul ξ]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem sum_dbar_angleForm_single : ∀ (D n : ℕ) (a a' : V D → ℝ) (q : V D → ℂ) (z ξ : V D), ContDiffAt ℝ 2 a z → ContDiffAt ℝ 2 a' z → ContDiffAt ℝ 2 q z → 0 < a z → 0 < a' z → ∑ j, ∑ l, ξ j * dbar (CurveDens.angleForm n a a' q (EuclideanSpace.single j 1)) z (EuclideanSpace.single l 1) * starRingEnd ℂ (ξ l) = dbar (CurveDens.angleForm n a a' q ξ) z ξ := by
  intro D n a a' q z ξ ha ha' hq h0 h0'
  have hd : ∀ η : V D, DifferentiableAt ℝ (angleForm n a a' q η) z := fun η =>
    ((angleForm_props _ n a a' q η z).2.1 ha ha' hq h0 h0').differentiableAt one_ne_zero
  have he : angleForm n a a' q ξ =
      fun x => ∑ j, ξ j • angleForm n a a' q (EuclideanSpace.single j 1) x :=
    funext fun x => angleForm_eq_sum_coeff n a a' q ξ x
  rw [he, dbar_sum (A := fun j x => ξ j • angleForm n a a' q (EuclideanSpace.single j 1) x)
    fun j _ => (hd _).fun_const_smul (ξ j), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dbar_const_smul _ (hd _), ContinuousLinearMap.smul_apply, smul_eq_mul]
  generalize dbar (angleForm n a a' q (EuclideanSpace.single j 1)) z = T
  have hT : T ξ = ∑ l, starRingEnd ℂ (ξ l) * T (EuclideanSpace.single l 1) := by
    conv_lhs => rw [vec_eq_sum_single_smul ξ]
    simp only [map_sum, map_smulₛₗ, smul_eq_mul]
  rw [hT, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.CurveDens
