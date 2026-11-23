import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothPtLift

set_option autoImplicit false

theorem exists_lift (U S : Scheme.{0}) (p : U ⟶ S) [Smooth p] (C : Type) [CommRing C] [IsLocalRing C]
    (I : Ideal C) (hI : I ^ 2 = ⊥) (s : Sp C ⟶ S) (u₀ : Sp (C ⧸ I) ⟶ U)
    (hw : u₀ ≫ p = spMap (Ideal.Quotient.mk I) ≫ s) :
    ∃ u : Sp C ⟶ U, spMap (Ideal.Quotient.mk I) ≫ u = u₀ ∧ u ≫ p = s := by
  have hItop : I ≠ ⊤ := by
    rintro rfl
    have h1 : (1 : C) ∈ (⊤ : Ideal C) ^ 2 := by rw [Ideal.top_pow]; exact Submodule.mem_top
    rw [hI, Ideal.mem_bot] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (C ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let t₀ : Sp (C ⧸ I) := IsLocalRing.closedPoint (C ⧸ I)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p (u₀ t₀))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (a := u₀ t₀) hxW (W.2.preimage p.continuous)
  haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have hmap : (spMap (Ideal.Quotient.mk I)) t₀ = IsLocalRing.closedPoint C :=
    IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I)
  have hsW : Set.range s ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    have h1 : s (IsLocalRing.closedPoint C) ∈ W := by
      rw [← hmap, ← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply]
      exact hxW
    exact ((IsLocalRing.specializes_closedPoint z).map s.continuous).mem_open W.2 h1
  have hu₀V : Set.range u₀ ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map u₀.continuous).mem_open V.2 hxV
  obtain ⟨a, ha⟩ : ∃ a, Spec.map a = IsOpenImmersion.lift hW.fromSpec s hsW := ⟨_, Spec.map_preimage _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b, Spec.map b = IsOpenImmersion.lift hV.fromSpec u₀ hu₀V :=
    ⟨_, Spec.map_preimage _⟩
  have key : p.appLE W V hVW ≫ b₀ = a ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono hW.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec p hW hV hVW, hb₀, ha, IsOpenImmersion.lift_fac_assoc,
      IsOpenImmersion.lift_fac, hw]
  have hsm := p.smooth_appLE hW hV hVW
  algebraize [(p.appLE W V hVW).hom, a.hom]
  let g : Γ(U, V) →ₐ[Γ(S, W)] C ⧸ I :=
    { b₀.hom with
      commutes' := fun r => by
        have := congrArg (fun f => f.hom r) key
        exact this }
  let b := Algebra.FormallySmooth.lift I ⟨2, hI⟩ g
  refine ⟨Spec.map (CommRingCat.ofHom b.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · have e : CommRingCat.ofHom b.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) = b₀ := by
      ext x
      exact Algebra.FormallySmooth.mk_lift I ⟨2, hI⟩ g x
    rw [← Category.assoc, ← Spec.map_comp, e, hb₀, IsOpenImmersion.lift_fac]
  · have e : p.appLE W V hVW ≫ CommRingCat.ofHom b.toRingHom = a := by
      ext r
      exact b.commutes r
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hW hV hVW, ← Category.assoc,
      ← Spec.map_comp, e, ha, IsOpenImmersion.lift_fac]

end GlobalTheory.SmoothPtLift
