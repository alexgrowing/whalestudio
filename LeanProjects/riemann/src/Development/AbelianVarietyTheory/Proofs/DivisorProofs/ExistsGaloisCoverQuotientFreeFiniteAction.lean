import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM

theorem exists_isGaloisCover_of_isQProjOver_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  intro K _ _ X s Ga _ _ ρ hs h1 hm hρ hfree
  let τ := autOfRightAction ρ h1 hm
  have := OrbitsInAffineOpens.of_isQProjOver hs τ
  obtain ⟨_, _, _⟩ := isSeparated_finiteType_of_isQProjOver hs
  have hτ : ∀ a, (τ a).hom ≫ s = s := fun a ↦ hρ a⁻¹
  have hf : IsFreeAction τ := .of_isAlgClosed fun k _ _ y a h ↦ inv_eq_one.mp (hfree k y a⁻¹ h)
  refine ⟨finiteQuotient τ, finiteQuotient.π τ, finiteQuotient.desc τ s hτ,
    finiteQuotient.π_desc τ s hτ, ⟨‹_›, h1, hm, fun a ↦ ?_,
      finiteQuotient.isFinite_π_of_isFreeAction hf, finiteQuotient.etale_π hf, inferInstance,
      fun k _ _ y y' e ↦ ?_⟩, inferInstance, inferInstance, inferInstance⟩
  · have := finiteQuotient.comp_π τ a⁻¹
    rwa [autOfRightAction_hom, inv_inv] at this
  · obtain ⟨a, ha⟩ := (finiteQuotient.comp_π_eq_iff τ y y').mp e
    have ha : y ≫ ρ a⁻¹ = y' := ha
    refine ⟨a⁻¹, ha, fun c hc ↦ ?_⟩
    have hc : y ≫ ρ c = y' := hc
    have : y ≫ ρ (c * a) = y := by
      rw [hm, reassoc_of% hc, ← ha, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
    exact eq_inv_of_mul_eq_one_left (hfree k y _ this)

end GlobalTheory.ZM
