import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsConnected
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_connected : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ), ConnectedSpace (Pts Y σ) := by
  first | exact @GlobalTheory.Mean4O.connectedSpace_pts | exact GlobalTheory.Mean4O.connectedSpace_pts | (intros; apply GlobalTheory.Mean4O.connectedSpace_pts <;> assumption)
