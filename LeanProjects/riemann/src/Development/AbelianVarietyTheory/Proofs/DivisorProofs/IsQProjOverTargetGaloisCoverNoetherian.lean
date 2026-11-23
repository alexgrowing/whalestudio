import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GaloisQuotientRing
open GlobalTheory.GaloisQuotient

theorem isQProjOver_of_isGaloisCover : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  intro K _ _ X Y π sY Ga _ ρ hG _ _ hX
  have := hG.finite
  let τ : Ga →* Aut X := MonoidHom.mk'
    (fun a => (⟨ρ a⁻¹, ρ a, by rw [← hG.mul, inv_mul_cancel, hG.one], by rw [← hG.mul, mul_inv_cancel, hG.one]⟩ :
      X ≅ X))
    fun a c => Iso.ext (by
      change ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹
      rw [mul_inv_rev, hG.mul])
  have := OrbitsInAffineOpens.of_isQProjOver hX τ
  have hq := finiteQuotient.isAffineQuotient τ
  have hD := (GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hG).1
  obtain ⟨u, hu, -⟩ := hD _ (finiteQuotient.π τ) fun a => by
    simpa only [inv_inv] using (show ρ a⁻¹⁻¹ ≫ _ = _ from hq.comp_eq a⁻¹)
  let v := hq.desc π fun a => hG.inv a⁻¹
  have hv : finiteQuotient.π τ ≫ v = π := hq.comp_desc _ _
  have : IsIso u := ⟨v, (hD Y π hG.inv).unique (by rw [reassoc_of% hu, hv]) (Category.comp_id _),
    hq.hom_ext (by rw [reassoc_of% hv, hu, Category.comp_id])⟩
  obtain ⟨L, hL⟩ := exists_isAmpleLB_of_isAffineQuotient hq hX
  exact (hL.pull_of_isAffineHom u).isQProjOver sY

end GlobalTheory.GaloisQuotientRing
