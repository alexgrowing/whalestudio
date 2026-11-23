import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] :
    Function.Injective (jK R).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom h
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom x) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := fun x =>
    congrArg (fun f => f.hom x) e
  rw [h3, h3] at h2
  have h4 := IsFractionRing.injective R (FractionRing R) h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h4
  simpa using this

theorem Modif.gp_appTop_injective {R : Type} [CommRing R] [IsDomain R] (M : Modif R) :
    Function.Injective M.gp.appTop.hom := by
  haveI := M.integral
  haveI := M.dominant
  rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := M.gp.denseRange.exists_mem_open (M.S.basicOpen s).isOpen ⟨x, hx⟩
  have : y ∈ M.gp ⁻¹ᵁ M.S.basicOpen s := hy
  rw [Scheme.preimage_basicOpen_top, hs, Scheme.basicOpen_zero] at this
  exact absurd this (by simp)

theorem Modif.appTop_comp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (a : Γ(Sp R, ⊤)) :
    M.gp.appTop.hom (M.π.appTop.hom a) = (jK R).appTop.hom a := by
  rw [← M.gp_π, Scheme.Hom.comp_appTop]
  rfl

theorem Modif.appTop_bijective_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (M : Modif R), Function.Bijective M.π.appTop.hom ∧ Surjective M.π := by
  intro R _ _ _ _ M
  haveI := M.proper
  haveI := M.integral
  have hinj : Function.Injective M.π.appTop.hom := fun a b h => jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  refine ⟨⟨hinj, fun b => ?_⟩, ⟨?_⟩⟩
  ·
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed M.π b
    let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let eK := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have h3 : ∀ x, eK ((jK R).appTop.hom x) = algebraMap R (FractionRing R) (eR x) := fun x =>
      congrArg (fun f => f.hom x) e
    have hc : IsIntegral R (eK (M.gp.appTop.hom b)) := by
      refine ⟨p.map eR.toRingHom, hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap R (FractionRing R)).comp eR.toRingHom =
          (eK.toRingHom.comp M.gp.appTop.hom).comp M.π.appTop.hom := by
        ext x
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [M.appTop_comp, h3]
      rw [this]
      calc _ = (eK.toRingHom.comp M.gp.appTop.hom) (p.eval₂ M.π.appTop.hom b) :=
            (Polynomial.hom_eval₂ _ _ _ _).symm
        _ = 0 := by rw [hp, map_zero]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc
    refine ⟨eR.symm r, M.gp_appTop_injective (eK.injective ?_)⟩
    rw [M.appTop_comp, h3, RingEquiv.apply_symm_apply, hr]
  ·
    have hcl : IsClosed (Set.range M.π) := (M.π.isClosedMap).isClosed_range
    have hd : Dense (Set.range (jK R)) := (Modif.self R).dominant.denseRange
    have hsub : Set.range (jK R) ⊆ Set.range M.π := by
      rintro _ ⟨y, rfl⟩
      exact ⟨M.gp y, by rw [← Scheme.Hom.comp_apply, M.gp_π]⟩
    have := (hd.mono hsub).closure_eq
    rw [hcl.closure_eq] at this
    exact Set.range_eq_univ.1 this

end GlobalTheory.Mum
