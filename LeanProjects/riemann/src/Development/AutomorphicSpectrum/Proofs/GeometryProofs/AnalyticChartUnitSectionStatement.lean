import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartUnitSection
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_chart_unit_section : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U N : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T t : Ω) (v : Γ(X, N)) (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsCptGen ξ → IsChart s B Y → b₁ ∈ B → (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) → N ≤ U → (∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W) → IsUnit v → (∀ (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ N), genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q h v) = t / T) → T ≠ 0 → ExtendsUnitAt s (RingHom.id ℂ) ξ W F t (Y b₁) → ∃ (B₂ : Set (Fin d → ℂ)) (H : (Fin d → ℂ) → ℂ), b₁ ∈ B₂ ∧ HChart s ξ W U F T B₂ Y H := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_hChart_of_extendsUnitAt | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_hChart_of_extendsUnitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_hChart_of_extendsUnitAt <;> assumption)
