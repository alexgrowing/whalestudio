import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowLemmaQuasiProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NoetherianIntegralClosedCoverStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_proper_qproj_cover : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (n : ℕ) (Y : Fin n → Scheme.{0}) (π : ∀ i, Y i ⟶ X), (∀ i, IsProper (π i) ∧ IsQProjOver (π i ≫ p)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (π i) := by
  intro k _ _ X p hs hl hq
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hC : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hN : IsNoetherian X := { }
  obtain ⟨n, Z, j, hj, hcov⟩ := GlobalTheory.T.noetherian_integral_closed_cover X
  have key : ∀ i, ∃ (X' : Scheme.{0}) (π : X' ⟶ Z i), IsProper π ∧ Surjective π ∧
      IsQProjOver (π ≫ j i ≫ p) := by
    intro i
    have := (hj i).1
    have := (hj i).2
    exact GlobalTheory.T.chow_lemma_quasi_projective k (Z i) (j i ≫ p) inferInstance inferInstance inferInstance
  choose Y π hp hsurj hqp using key
  refine ⟨n, Y, fun i => π i ≫ j i, fun i => ?_, fun x => ?_⟩
  · have := (hj i).2
    have := hp i
    refine ⟨inferInstance, ?_⟩
    rw [Category.assoc]
    exact hqp i
  · obtain ⟨i, z, rfl⟩ := hcov x
    obtain ⟨y, rfl⟩ := (hsurj i).surj z
    exact ⟨i, y, by simp⟩

end GlobalTheory.CompanionTheory.Ar.Approx
