import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsIrreducibleConnected
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
theorem _root_.GlobalTheory.T.flag_bundle_points_irreducible_connected : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → ∀ (L : Type) [Field L] (q₁ q₂ : Spec (CommRingCat.of L) ⟶ Y), q₁ ≫ π = q₂ ≫ π → ∃ (T : Scheme.{0}) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (f : T ⟶ Y), IrreducibleSpace T ∧ t₁ ≫ f = q₁ ∧ t₂ ≫ f = q₂ := by
  first | exact @GlobalTheory.FlagConnect.exists_irreducible_through | exact GlobalTheory.FlagConnect.exists_irreducible_through | (intros; apply GlobalTheory.FlagConnect.exists_irreducible_through <;> assumption)
