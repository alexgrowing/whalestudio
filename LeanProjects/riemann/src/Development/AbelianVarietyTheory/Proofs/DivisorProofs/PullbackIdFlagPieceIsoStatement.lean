import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIdFlagPieceIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_id_flag_piece_iso : ∀ {B Y : Scheme.{0}} (π : Y ⟶ B) (E : B.Modules) (F : Y.Modules)
    (ι : F ⟶ (Scheme.Modules.pullback π).obj E) (w : 𝟙 Y ≫ π = π),
    ∃ e : (Scheme.Modules.pullback (𝟙 Y)).obj F ≅ F, e.hom ≫ ι =
      (Scheme.Modules.pullback (𝟙 Y)).map ι ≫ (Scheme.Modules.pullbackComp (𝟙 Y) π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E := by
  first | exact @GlobalTheory.pullback_id_lift_step_self | exact GlobalTheory.pullback_id_lift_step_self | (intros; apply GlobalTheory.pullback_id_lift_step_self <;> assumption)
