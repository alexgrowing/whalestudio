import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_lattice_vector_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → (Z.eig τ).IsVBOn Z.genFib D.p (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsVBOn Z.genFib D.q (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) ∧ (∀ x ∈ Z.genFib, ∃ g : ℕ, ∃ b : Fin g → Z.V, Z.M.lat.IsFrameAt b x ∧ ∀ σ' : E →+* ℂ, ∃ S : Finset (Fin g), Z.eig σ' x = Submodule.span (regAt _ x) (b '' S)) ∧ Z.genFib.Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib | exact GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib <;> assumption)
