import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricGrLBPullFlag
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grLB_pull_isometric_pullFlag : ∀ (k : Type) [CommRing k] (B Y B' : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (g : B' ⟶ B) (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n) (w' : Limits.pullback.snd π g ≫ g ≫ q = Limits.pullback.fst π g ≫ p) (i : Fin n), ((VMetric.grLB fl i (H.pull π w)).pull (Limits.pullback.fst π g) rfl).Isometric (VMetric.grLB (FlagBaseChange.pullFlag π g fl) i ((H.pull g rfl).pull (Limits.pullback.snd π g) w')) := by
  first | exact @GlobalTheory.FlagBaseChange.isometric_grLB_pullFlag | exact GlobalTheory.FlagBaseChange.isometric_grLB_pullFlag | (intros; apply GlobalTheory.FlagBaseChange.isometric_grLB_pullFlag <;> assumption)
