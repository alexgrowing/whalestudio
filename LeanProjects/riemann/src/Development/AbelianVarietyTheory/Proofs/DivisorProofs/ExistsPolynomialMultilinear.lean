import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.SelfInterPoly

theorem exists_polynomial_multilinear {A : Type*} {ι : Type} [AddCommGroup A] [Fintype ι]
    (f : MultilinearMap ℤ (fun _ : ι => A) ℤ) (a b : A) :
    ∃ P : Polynomial ℝ, ∀ m : ℕ, (f (fun _ => a + m • b) : ℝ) = P.eval (m : ℝ) := by
  classical
  refine ⟨∑ S : Finset ι, Polynomial.C (f (S.piecewise (fun _ => b) (fun _ => a)) : ℝ) *
    Polynomial.X ^ S.card, fun m => ?_⟩
  have e : (fun _ : ι => a + m • b) = (fun _ : ι => (m : ℤ) • b) + (fun _ : ι => a) := by
    funext i
    simp [add_comm]
  rw [e, f.map_add_univ, Polynomial.eval_finsetSum, Int.cast_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have e₂ : S.piecewise (fun _ : ι => (m : ℤ) • b) (fun _ : ι => a) =
      S.piecewise (fun i => (fun _ : ι => (m : ℤ)) i • S.piecewise (fun _ => b) (fun _ => a) i)
        (S.piecewise (fun _ => b) (fun _ => a)) := by
    funext i
    by_cases h : i ∈ S <;> simp [h]
  rw [e₂, f.map_piecewise_smul]
  simp [mul_comm]

theorem exists_polynomial_topSelf : ∀ (Y : Var ℂ) (L H : LB Y.X), L.IsLB → H.IsLB → ∃ P : Polynomial ℝ, P.eval 0 = (topSelfIntersection ℂ L Y.dim : ℝ) ∧ ∀ m : ℕ, (topSelfIntersection ℂ (CechPic.tens L (lbPow H m)) Y.dim : ℝ) = P.eval (m : ℝ) := by
  intro Y L H hL hH
  have hv := diffVanish_chiPic_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver
    (d := Y.dim) (by rw [QCoh.suppDim_structureModule, Y.topologicalKrullDim_eq])
  have key : ∀ (M : LB Y.X) (hM : M.IsLB), topSelfIntersection ℂ M Y.dim = hv.form fun _ => cls M hM :=
    fun M hM => (interNum_eq_multiDiff ℂ _ fun _ => hM).trans (hv.form_apply _ 0).symm
  obtain ⟨P, hP⟩ := exists_polynomial_multilinear hv.form (cls L hL) (cls H hH)
  refine ⟨P, ?_, fun m => ?_⟩
  · have h0 := hP 0
    rw [zero_nsmul, add_zero, Nat.cast_zero] at h0
    rw [key L hL, h0]
  · rw [key _ (isLB_tens hL (isLB_lbPow hH m)), cls_tens hL (isLB_lbPow hH m), cls_lbPow hH, hP]

end GlobalTheory.SelfInterPoly
