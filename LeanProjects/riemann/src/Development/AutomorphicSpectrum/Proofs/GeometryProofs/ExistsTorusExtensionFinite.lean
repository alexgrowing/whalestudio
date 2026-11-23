import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_finite_torusExtension_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) := by
  intro S G _ hG L _ _ z
  have h₀ : IsSemiAbelian ((Over.pullback z).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  obtain ⟨T⟩ := h₀.fibres (AlgebraicClosure L) (spMap (algebraMap L (AlgebraicClosure L)))
  obtain ⟨k', hk, ⟨T'⟩⟩ := GlobalTheory.exists_finite_torusExtension L (AlgebraicClosure L) ((Over.pullback z).obj G)
    inferInstance h₀.quasiCompact h₀.separated ⟨T⟩
  refine ⟨k', inferInstance, inferInstance, hk, ?_⟩
  haveI : IsMonHom (pullCompIso (spMap (algebraMap L k')) z G).symm.hom :=
    inferInstanceAs (IsMonHom (pullCompIso (spMap (algebraMap L k')) z G).inv)
  exact ⟨torusExtOfIso (pullCompIso (spMap (algebraMap L k')) z G).symm T'⟩

end GlobalTheory.CompanionTheory.Ar
