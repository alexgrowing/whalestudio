import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionAbelianQuotient
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
theorem _root_.GlobalTheory.T.torus_extension_abelian_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [CharZero L] (tK : SAB H (Sp L)) (τ : TorusExtension tK.G), ∃ (tB : SAB H (Sp L)) (e : τ.B ≅ tB.G), (letI := τ.grpB; IsMonHom e.hom) ∧ (∀ a, tK.act.act a ≫ τ.q ≫ e.hom = τ.q ≫ e.hom ≫ tB.act.act a) ∧ LBIso tK.PP.L (tB.PP.L.pull (τ.q ≫ e.hom).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbB.exists_triple | exact GlobalTheory.CompanionTheory.Ar.AbB.exists_triple | (intros; apply GlobalTheory.CompanionTheory.Ar.AbB.exists_triple <;> assumption)
