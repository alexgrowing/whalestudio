import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalWeightPotentialChart
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory
open ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_weight_potential_chart : ∀ (D : D7) (O : Setup D) (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (R : O.Reads A T H) (c : O.s.Comp) (a : Fin ((T.M c).n + 1)) (u : D.what₂.Tau → Fin O.N → ℝ) (x : (T.M c).X a), GlobalTheory.ShFam.IsPotential (AnRead.all (O.var c).str ((R.man c).ε a) (O.var c).dim) (thW O.met.h0 c ((R.man c).ε a) u) ((R.man c).pt a '' ((T.F c).th u a).U x) (fun y => 2 * ((T.F c).th u a).φ x (((R.man c).pt a).symm y)) := by
  first | exact @GlobalTheory.FormPotBridge.thW_isPotential | exact GlobalTheory.FormPotBridge.thW_isPotential | (intros; apply GlobalTheory.FormPotBridge.thW_isPotential <;> assumption)
