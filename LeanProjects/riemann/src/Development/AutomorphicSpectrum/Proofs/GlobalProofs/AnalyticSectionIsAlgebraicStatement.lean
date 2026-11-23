import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticSectionIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_section_is_algebraic : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → IsProper p → ∀ (R : AnRead p (RingHom.id ℂ) D) (B : LB Y), B.IsLB → ∀ s ∈ R.holSec B, ∃ t : B.Sec, secVal p (RingHom.id ℂ) t = s := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.holomorphicSections_algebraic_of_isProper | exact GlobalTheory.CompanionTheory.Gaga.holomorphicSections_algebraic_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Gaga.holomorphicSections_algebraic_of_isProper <;> assumption)
