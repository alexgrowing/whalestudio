import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSectionLiftsLocally
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_section_lifts_locally : ∀ {X : Scheme.{0}} {M : X.Modules} {N : ℕ} (fl : Vert.Flag M N) (i : Fin N) (U : X.Opens)
    (e : Γ(fl.gr i, U)) (y : X), y ∈ U →
    ∃ (W : X.Opens) (hW : W ≤ U) (t : Γ(fl.F i.succ, W)), y ∈ W ∧ (fl.π i).app W t = Twist.resM _ hW e := by
  first | exact @GlobalTheory.Vert.Flag.exists_local_lift_gr | exact GlobalTheory.Vert.Flag.exists_local_lift_gr | (intros; apply GlobalTheory.Vert.Flag.exists_local_lift_gr <;> assumption)
