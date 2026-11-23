import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsClopenSpecializationsGenPtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem genPt_mem_of_dense_open : ∀ (W : Scheme.{0}) [IsLocallyNoetherian W] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W) (U : W.Opens), IsCptGen ξ → Dense (U : Set W) → genPt ξ ∈ U := by
  intro W _ Ω _ ξ U hξ hU
  have hcl := GlobalTheory.T.isClopen_specializations_genPt W Ω ξ hξ
  obtain ⟨q, hq, hqU⟩ := hU.inter_open_nonempty _ hcl.isOpen ⟨genPt ξ, specializes_rfl⟩
  exact hq.mem_open U.isOpen hqU

end GlobalTheory.CompanionTheory.Ar.SncBase
