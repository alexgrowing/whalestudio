import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusExtensionFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionAbelianQuotientStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAbPartTorusPos

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem abPart_exists (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ S) :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L'), Nonempty (AbPart t (spMap e ≫ z)) := by
  obtain ⟨L', _, _, hfin, ⟨τ⟩⟩ := GlobalTheory.T.exists_torus_extension_finite S t.G t.semi L z
  have : CharZero L' := charZero_of_injective_algebraMap (algebraMap L L').injective
  have : NumberField L' := NumberField.of_module_finite L L'
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.proved_CubePullSt (spMap (algebraMap L L') ≫ z) t
  obtain ⟨tB, e, he, ha, hp⟩ := GlobalTheory.T.torus_extension_abelian_quotient E H L'
    ⟨(Over.pullback (spMap (algebraMap L L') ≫ z)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ τ
  exact ⟨L', _, inferInstance, algebraMap L L', ⟨⟨_, m, τ, tB, e, he, ha, hp⟩⟩⟩

end GlobalTheory.CompanionTheory.Ar
