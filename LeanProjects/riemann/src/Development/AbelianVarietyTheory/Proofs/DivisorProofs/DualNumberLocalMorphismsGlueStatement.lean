import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberLocalMorphismsGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_number_local_morphisms_glue : ∀ {L : Type} [CommRing L] {s : Set L}, Ideal.span s = ⊤ → ∀ {Y : Scheme.{0}} (w : ∀ a : s, Sp (DualNumber (Localization.Away (a : L))) ⟶ Y), (∀ a b : s, spMap (Formalism.L2.Pj.dualMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away (a : L)) (P := Localization.Away ((a : L) * b)) (a : L) (b : L))) ≫ w a = spMap (Formalism.L2.Pj.dualMap (IsLocalization.Away.awayToAwayLeft (S := Localization.Away (b : L)) (P := Localization.Away ((a : L) * b)) (b : L) (a : L))) ≫ w b) → ∃ w₀ : Sp (DualNumber L) ⟶ Y, ∀ a : s, spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w₀ = w a := by
  first | exact @GlobalTheory.GlueTanAway.glue_away_dual | exact GlobalTheory.GlueTanAway.glue_away_dual | (intros; apply GlobalTheory.GlueTanAway.glue_away_dual <;> assumption)
