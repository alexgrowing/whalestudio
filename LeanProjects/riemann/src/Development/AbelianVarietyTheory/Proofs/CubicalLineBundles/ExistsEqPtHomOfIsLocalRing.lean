import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory

theorem exists_eq_ptHom_of_isLocalRing : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (A : Type) [CommRing A] [IsLocalRing A] (ρ : R →+* A) (x : Sp A ⟶ scheme W), x ≫ toSpec W = spMap ρ → ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
  intro R _ W A _ _ ρ x hx
  have key : ∀ i : Fin 3, x (IsLocalRing.closedPoint A) ∈ coordOpen W i →
      ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
    intro i hi
    have htop : x ⁻¹ᵁ coordOpen W i = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff (R := A) (x ⁻¹ᵁ coordOpen W i)).mp hi
    have hr : Set.range x ⊆ Set.range (awayChart W i) := by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ x ⁻¹ᵁ coordOpen W i := htop.ge trivial
      rw [← opensRange_awayChart] at hy
      exact hy
    obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift (awayChart W i) x hr)
    have hx' : x = Spec.map (CommRingCat.ofHom g.hom) ≫ awayChart W i := by
      rw [CommRingCat.ofHom_hom, hg, IsOpenImmersion.lift_fac]
    rw [SpecMap_awayChart] at hx'
    have hρ : g.hom.comp (awayConst W i) = ρ := by
      rw [hx', ptHom_toSpec] at hx
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
    subst hρ
    exact ⟨_, _, hx'⟩
  have h : x (IsLocalRing.closedPoint A) ∈ coordOpen W 1 ⊔ coordOpen W 2 := by
    rw [coordOpen_one_sup_coordOpen_two]
    trivial
  rcases h with h | h
  · exact key 1 h
  · exact key 2 h

end GlobalTheory
