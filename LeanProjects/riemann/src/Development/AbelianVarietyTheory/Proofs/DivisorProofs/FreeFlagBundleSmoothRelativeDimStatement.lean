import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFlagBundleSmoothRelativeDim
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
theorem _root_.GlobalTheory.T.free_flag_bundle_smooth_relative_dim : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (r : ι → ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a)))) (r a)), IsFlagBundle π (fun a => SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a))) r fl ∧ SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  first | exact @GlobalTheory.FlagFreeSmooth.main | exact GlobalTheory.FlagFreeSmooth.main | (intros; apply GlobalTheory.FlagFreeSmooth.main <;> assumption)
