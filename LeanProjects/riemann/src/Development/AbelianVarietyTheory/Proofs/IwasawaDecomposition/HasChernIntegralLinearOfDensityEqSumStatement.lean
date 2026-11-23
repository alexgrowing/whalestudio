import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (R : MvPolynomial (ι × ℕ) ℝ) (J : Type) [Fintype J] (M : J → ℕ) (E' : ∀ j, Fr (ratOf X) (fun _ : Unit => M j) 0) (H' : ∀ j, Mat (fun _ : Unit => M j) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => M j) ℂ) (R' : MvPolynomial (Unit × ℕ) ℝ) (a t : J → ℝ), IsMetricOn E O H → (∀ j, IsMetricOn (E' j) O (H' j)) → (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∃ A ∈ E.S (under y), ∃ B : ∀ j, Mat (fun _ : Unit => M j) X.Fn, (∀ j, B j ∈ (E' j).S (under y)) ∧ chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ∑ j, a j * chernTop R' (fun v => H' j (B j) (c.e.symm v)) (c.e y)) → (∀ j, HasChernIntegral (E' j) O (H' j) R' (t j)) → HasChernIntegral E O H R (∑ j, a j * t j) := by
  first | exact @GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum | exact GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum | (intros; apply GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum <;> assumption)
