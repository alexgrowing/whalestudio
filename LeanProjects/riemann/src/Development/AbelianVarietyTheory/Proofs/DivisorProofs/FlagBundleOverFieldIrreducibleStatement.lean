import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleOverFieldIrreducible
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_over_field_irreducible : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of K)) (ι : Type) [Fintype ι] (E : ι → (Spec (CommRingCat.of K)).Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  first | exact @GlobalTheory.FlagIrrFld.irreducibleSpace_of_isFlagBundle | exact GlobalTheory.FlagIrrFld.irreducibleSpace_of_isFlagBundle | (intros; apply GlobalTheory.FlagIrrFld.irreducibleSpace_of_isFlagBundle <;> assumption)
