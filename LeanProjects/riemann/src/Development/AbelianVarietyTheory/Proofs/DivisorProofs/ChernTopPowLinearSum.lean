import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChernWeilLine

theorem chernTop_pow_sum_c1 {n : ℕ} {ι : Type} [Fintype ι] (t : ι → ℝ) (G : V n → Mat (fun _ : ι => 1) ℂ) (v : V n) :
    chernTop ((∑ i, C (t i) * X (i, 1)) ^ n) G v = n.factorial / Real.pi ^ n *
      (∑ i, (t i : ℂ) • Matrix.of fun a b => curv (fun u => G u i) v (coordVec a) (coordVec b) 0 0).det.re := by
  have e (i : ι) : chernPoly (fun u => G u i) v 1 = curvPoly (fun u => G u i) v 0 0 := by
    rw [chernPoly, Matrix.coeff_charpolyRev_eq_neg_trace]
    simp [Matrix.trace]
  set M : Matrix (Fin n) (Fin n) ℂ :=
    ∑ i, (t i : ℂ) • Matrix.of fun a b => curv (fun u => G u i) v (coordVec a) (coordVec b) 0 0 with hM
  have hs : aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) (∑ i, C (t i) * X (i, 1)) =
      ∑ a, ∑ b, C (M a b) * X (a, b) := by
    simp only [map_sum, map_mul, aeval_C, aeval_X, e, curvPoly, Matrix.of_apply, hM, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.algebraMap_apply, mul_assoc]
    rfl
  rw [chernTop, map_pow, hs, topCoeff_pow]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm]

end GlobalTheory.ChernWeilLine
