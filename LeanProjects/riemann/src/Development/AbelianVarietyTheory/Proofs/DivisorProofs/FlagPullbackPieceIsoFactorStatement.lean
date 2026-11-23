import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackPieceIsoFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagModelOfIsIsometry
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pullback_piece_iso_factor : ∀ {k : Type} [CommRing k] {B Y₀ Y : Scheme.{0}} (p : B ⟶ Sp k) (π₀ : Y₀ ⟶ B)
    (π : Y ⟶ B) (E : B.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf)
    (fl₀ : Vert.Flag ((Scheme.Modules.pullback π₀).obj E) r) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r)
    (g' : Y ⟶ Y₀) (w : g' ≫ π₀ = π),
    (∀ i, ∃ e : (Scheme.Modules.pullback g').obj (fl₀.F i) ≅ fl.F i, e.hom ≫ fl.ι i =
      (Scheme.Modules.pullback g').map (fl₀.ι i) ≫ (Scheme.Modules.pullbackComp g' π₀).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E) →
    ∀ (hf : g' ≫ π₀ ≫ p = π ≫ p) (i : Fin r),
    (VMetric.grLB fl i (H.pull π rfl)).Isometric ((VMetric.grLB fl₀ i (H.pull π₀ rfl)).pull g' hf) := by
  first | exact @GlobalTheory.VMetric.isometric_grLB_of_steps_pull | exact GlobalTheory.VMetric.isometric_grLB_of_steps_pull | (intros; apply GlobalTheory.VMetric.isometric_grLB_of_steps_pull <;> assumption)
