import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagDetIsometric
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_flag_det_isometric : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N),
    GlobalTheory.FlagZ.Taut.IsTaut ι N fl → ∀ (a : ι) (l : Fin (N + 1)),
    (VMetric.det (((HermVB.std (𝟙 (Sp ℤ)) N).cInf.pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _)).restrict
      ((fl a).isSubbundle l) ((fl a).isVB l))).Isometric (GlobalTheory.FlagZ.flDet a l).dual := by
  first | exact @GlobalTheory.FlagZ.StepDet.isometric_det_step | exact GlobalTheory.FlagZ.StepDet.isometric_det_step | (intros; apply GlobalTheory.FlagZ.StepDet.isometric_det_step <;> assumption)
