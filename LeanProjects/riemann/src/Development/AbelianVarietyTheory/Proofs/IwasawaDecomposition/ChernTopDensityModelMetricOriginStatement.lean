import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopDensityModelMetricOrigin
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
open Formalism.DegreeFormula

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTop_density_model_metric_origin : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n), GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = GlobalTheory.TrueCx.grassConst p q ^ Fintype.card ι := by
  first | exact @GlobalTheory.DomainDens.chernTop_model_origin | exact GlobalTheory.DomainDens.chernTop_model_origin | (intros; apply GlobalTheory.DomainDens.chernTop_model_origin <;> assumption)
