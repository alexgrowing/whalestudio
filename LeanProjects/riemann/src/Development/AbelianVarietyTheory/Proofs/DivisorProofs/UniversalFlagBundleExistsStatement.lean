import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFlagBundleExists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_flag_bundle_exists : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ Sp ℤ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin (r a)))) (r a)), IsFlagBundle π (fun a => GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin (r a))) r fl := by
  first | exact @GlobalTheory.FlagFree.exists_isFlagBundle_freeModule | exact GlobalTheory.FlagFree.exists_isFlagBundle_freeModule | (intros; apply GlobalTheory.FlagFree.exists_isFlagBundle_freeModule <;> assumption)
