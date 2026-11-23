import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleLocallyFree
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_locally_free : ∀ (B : Scheme.{0}) (ι : Type) [Finite ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∀ b : B, ∃ U : B.Opens, b ∈ U ∧ ∀ a, Nonempty ((Scheme.Modules.pullback U.ι).obj (E a) ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin (r a))) := by
  first | exact @GlobalTheory.VB.exists_open_isVB_free_finite | exact GlobalTheory.VB.exists_open_isVB_free_finite | (intros; apply GlobalTheory.VB.exists_open_isVB_free_finite <;> assumption)
