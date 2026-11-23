import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polyRep_inducedBundle_and_metric : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (E : Fr (ratOf X) m 0), ∃ E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0, (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) ∧ ∀ (σ : F →+* ℂ) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∃ H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ, IsMetricOn E' O H' ∧ ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y) := by
  first | exact @GlobalTheory.GoodMetric.RepBundle.exists_repBundle | exact GlobalTheory.GoodMetric.RepBundle.exists_repBundle | (intros; apply GlobalTheory.GoodMetric.RepBundle.exists_repBundle <;> assumption)
