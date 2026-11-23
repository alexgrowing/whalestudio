import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionDivDetUnit
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOnPts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ShFam.Pad GlobalTheory.FlatSecCover

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_section_div_det_unit : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (B : ℝ) (τ : D.what₂.Tau) (z : (O.var c).X),
    UnitAt z (flatSec O.s O.Φ c τ / detFn O c B τ z) := by
  first | exact @GlobalTheory.FlatSecCover.unitAt_flatSec_div_detFn | exact GlobalTheory.FlatSecCover.unitAt_flatSec_div_detFn | (intros; apply GlobalTheory.FlatSecCover.unitAt_flatSec_div_detFn <;> assumption)
