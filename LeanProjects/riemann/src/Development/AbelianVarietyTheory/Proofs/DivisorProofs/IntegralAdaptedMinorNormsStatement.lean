import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedMinorNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adapted_minor_norms : ∀ {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ}
    (P : Matrix (Fin g) κ K), IntAdapted bl P →
    (∀ (w : κ ≃ Fin g) (k : ℕ), ‖minor bl w k P‖ ≤ 1) ∧ ∃ w : κ ≃ Fin g, ∀ k : ℕ, ‖minor bl w k P‖ = 1 := by
  first | exact @GlobalTheory.LieFilt.intAdapted_minor | exact GlobalTheory.LieFilt.intAdapted_minor | (intros; apply GlobalTheory.LieFilt.intAdapted_minor <;> assumption)
