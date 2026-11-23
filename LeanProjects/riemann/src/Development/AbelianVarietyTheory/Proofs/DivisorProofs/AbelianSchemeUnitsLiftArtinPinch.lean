import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.PinchUnitLift

theorem unit_lift (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀)
    (h : IsPullback f₁ f₂ g₁ g₂) [IsLocalRing P] (h₁ : Function.Surjective g₁) (h₂ : Function.Surjective g₂)
    (r : R₀) (hr : IsUnit r) : ∃ s : R₁, IsUnit s ∧ g₁ s = r := by
  rcases subsingleton_or_nontrivial R₀ with h0 | h0
  · exact ⟨1, isUnit_one, Subsingleton.elim _ _⟩
  have hf : Function.Surjective f₁ := by
    intro a
    obtain ⟨b, hb⟩ := h₂ (g₁ a)
    obtain ⟨p, hp, -⟩ := Types.exists_of_isPullback (h.map (forget CommRingCat)) a b hb.symm
    exact ⟨p, hp⟩
  haveI : Nontrivial R₁ := g₁.hom.domain_nontrivial
  haveI : IsLocalRing R₁ := IsLocalRing.of_surjective' f₁.hom hf
  haveI : IsLocalHom g₁.hom := IsLocalHom.of_surjective g₁.hom h₁
  obtain ⟨s, rfl⟩ := h₁ r
  exact ⟨s, IsUnit.of_map g₁.hom s hr, rfl⟩

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (B : Over (Spec R₀)) [GrpObj B], IsAbelianScheme B → ∀ (X₁ : Scheme.{0}) (q : X₁ ⟶ Spec R₁) (ρ : B.left ⟶ X₁), ρ ≫ q = B.hom ≫ Spec.map g₁ → ∀ u : Γ(B.left, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : B.left, gm ρ x ⊤ v = gm (𝟙 B.left) x ⊤ u := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ h₁ h₂ B _ hB X₁ q ρ hρ u
  have hb := GlobalTheory.globalFns_holds _ B hB
  obtain ⟨t, ht⟩ := hb.2 u.val
  obtain ⟨t', ht'⟩ := hb.2 (u⁻¹).val
  have htu : IsUnit t := by
    refine IsUnit.of_mul_eq_one t' (hb.1 ?_)
    rw [map_mul, map_one, ht, ht']
    exact u.mul_inv
  obtain ⟨s, hs, hst⟩ := unit_lift P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h h₁ h₂ ((Scheme.ΓSpecIso R₀).hom t)
    (htu.map (Scheme.ΓSpecIso R₀).hom.hom)
  have hv : IsUnit (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) := (hs.map _).map _
  refine ⟨hv.unit, fun x => Units.ext ?_⟩
  rw [gm_val ρ x ⊤ trivial, gm_val (𝟙 B.left) x ⊤ trivial]
  have e : ρ.appTop.hom (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) = u.val := by
    have e1 : ρ.appTop.hom (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) =
        (ρ ≫ q).appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s) := by
      rw [Scheme.Hom.comp_appTop]; rfl
    have e2 : (Spec.map g₁).appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s) = t := by
      have := congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_inv_naturality g₁)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [← this]
      have hst' : g₁.hom s = (Scheme.ΓSpecIso R₀).hom.hom t := hst
      rw [hst']
      exact (Scheme.ΓSpecIso R₀).hom_inv_id_apply t
    rw [e1, hρ, Scheme.Hom.comp_appTop, ← ht, ← e2]
    rfl
  exact congrArg (B.left.presheaf.germ ⊤ x trivial).hom e

end GlobalTheory.PinchUnitLift
