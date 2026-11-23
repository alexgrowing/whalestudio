import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpan
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_on_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S' S : Scheme.{0}) (t₀ : SAB H S') (t : SAB H S) (f : S' ⟶ S) (_ : SABMap t₀ t f) (z₀ : Sp ℂ ⟶ S') (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (z₀ ≫ f) V) (core : InnerProductSpace.Core ℂ V) (W : Set V), (0 : V) ∈ W → Submodule.span ℂ W = ⊤ → (∀ a ∈ W, ∀ b ∈ W, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b)) → ∀ a b : V, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span | exact GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span <;> assumption)
