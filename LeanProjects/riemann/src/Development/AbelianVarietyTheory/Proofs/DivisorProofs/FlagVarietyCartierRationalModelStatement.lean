import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyCartierRationalModel
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_cartier_rational_model : ∀ (ι : Type) [Fintype ι] (N : ℕ), ∃ (Y : GlobalTheory.ProjVar.Var ℚ) (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N) (gr : ι × Fin N → Y.Dv), IsPullback j Y.str (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)) ∧ Y.dim = dimFl ι N ∧ (∀ x, ∃ r, GlobalTheory.Cartier.Presents (gr x) ((GlobalTheory.FlagZ.grLine x).B.pull j) r) ∧ ∃ (X : GlobalTheory.ProjVar.Var ℚ) (E : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf X) (fun _ : ι => N) 0) (E' : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf Y) (fun _ : ι => N) (fun _ : ι => N)) (φ : X.Fn →ₐ[ℚ] Y.Fn) (f : Y.X ⟶ X.X), X.dim = 0 ∧ GlobalTheory.FlagBundle.Refines E E' φ f ∧ GlobalTheory.GoodMetric.IsGraded E' (fun x => gr (x.1, x.2)) := by
  first | exact @GlobalTheory.FlagQ.genericFibre_flagBundle | exact GlobalTheory.FlagQ.genericFibre_flagBundle | (intros; apply GlobalTheory.FlagQ.genericFibre_flagBundle <;> assumption)
