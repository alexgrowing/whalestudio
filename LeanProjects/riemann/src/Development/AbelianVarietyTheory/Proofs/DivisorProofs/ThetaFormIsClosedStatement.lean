import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFormIsClosed
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_form_is_closed : OnCore fun D O x _ => ∀ c (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin O.N → ℝ), GlobalTheory.Published.IsClosedForm (AnRead.all (O.var c).str σ (O.var c).dim) (thW (refMet x O.Φ) c σ u) := by
  first | exact @GlobalTheory.thW_refMet_isClosedForm | exact GlobalTheory.thW_refMet_isClosedForm | (intros; apply GlobalTheory.thW_refMet_isClosedForm <;> assumption)
