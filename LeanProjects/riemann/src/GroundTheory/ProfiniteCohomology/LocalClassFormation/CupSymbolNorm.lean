import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts.Projection
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
import GroundTheory.ProfiniteCohomology.ClassFormations.Corestriction
import GroundTheory.ProfiniteCohomology.CyclicCupProf
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.H0IsoHomCohomologyClassZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

section Comp

variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

def contCharComp (χ : Additive G →ₜ+ QZ) (φ : H →* G) (hφ : Continuous φ) : Additive H →ₜ+ QZ :=
  χ.comp ⟨MonoidHom.toAdditive φ, hφ⟩

@[simp]
theorem contCharComp_apply (χ : Additive G →ₜ+ QZ) (φ : H →* G) (hφ : Continuous φ) (x : H) :
    contCharComp χ φ hφ (Additive.ofMul x) = χ (Additive.ofMul (φ x)) :=
  rfl

end Comp

section Naturality

variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

def trivialIntResHom (φ : H →* G) : Rep.res φ (Rep.trivial ℤ G ℤ) ⟶ Rep.trivial ℤ H ℤ :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

theorem cohomologyMapAlong_charClassProf (φ : H →* G) (hφ : Continuous φ) (χ : Additive G →ₜ+ QZ) :
    (cohomologyMapAlong φ hφ (trivialIntResHom φ) 2).hom (charClassProf χ) =
      charClassProf (contCharComp χ φ hφ) := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_charClassProf χ
  obtain ⟨w', hw', hwc'⟩ := exists_cocycle_charClassProf (contCharComp χ φ hφ)
  rw [← hw, ← hw', cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cochainOf_cocycleι_cocyclesMapAlong]
  funext v
  rw [hwc', hwc]
  rfl

theorem cohomologyMapAlong_cupCharClassProf (φ : H →* G) (hφ : Continuous φ) {A : Rep ℤ G}
    {B : Rep ℤ H} [IsDiscreteRep A] [IsDiscreteRep B] (f : Rep.res φ A ⟶ B) (χ : Additive G →ₜ+ QZ)
    (a : A.ρ.invariants) (b : B.ρ.invariants) (hab : (b : B) = f.hom (a : A)) :
    (cohomologyMapAlong φ hφ f 2).hom ((cupCharClassProf A χ).hom a) =
      (cupCharClassProf B (contCharComp χ φ hφ)).hom b := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf A χ a
  obtain ⟨w', hw', hwc'⟩ := exists_cocycle_cupCharClassProf B (contCharComp χ φ hφ) b
  rw [← hw, ← hw', cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cochainOf_cocycleι_cocyclesMapAlong]
  funext v
  rw [hwc', hwc, hab]
  exact map_zsmul f.hom.toAddMonoidHom _ _

end Naturality

section CoresH0

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G) (A : Rep.{0} k G)

def coindConst (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)).ρ.invariants :=
  ⟨⟨fun _ => a.1, fun u _ => (a.2 u).symm⟩, fun _ => rfl⟩

noncomputable def invariantsNorm (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    A.ρ.invariants :=
  ((Rep.invariantsFunctor k G).map (coindTrace (U : Subgroup G) A)).hom (coindConst U A a)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
theorem coe_invariantsNorm (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    (invariantsNorm U A a : A) = ∑ c : G ⧸ (U : Subgroup G), A.ρ c.out (a : A) := by
  change (coindTrace (U : Subgroup G) A).hom (coindConst U A a).1 = _
  rw [coindTrace_hom_apply]
  rfl

variable [IsDiscreteRep A]

theorem cohomologyCores_H0Iso_inv (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    (cohomologyCores U A 0).hom ((H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a) =
      (H0Iso A).inv.hom (invariantsNorm U A a) := by
  have hs : (shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0).hom
      ((H0Iso (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))).inv.hom
        (coindConst U A a)) = (H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a := by
    have e := H0Iso_hom_cohomologyMapAlong (U : Subgroup G).subtype (continuous_subgroup_subtype _)
      (coindEvalOne (U : Subgroup G) (Rep.res (U : Subgroup G).subtype A))
      ((H0Iso (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))).inv.hom
        (coindConst U A a))
    rw [H0Iso_hom_inv_apply] at e
    rw [← H0Iso_inv_hom_apply (Rep.res (U : Subgroup G).subtype A)
      ((shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0).hom _)]
    congr 1
    exact Subtype.ext e
  rw [← hs]
  have hinv : ∀ x, (inv (shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0)).hom
      ((shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0).hom x) = x := fun x => by
    rw [← ModuleCat.comp_apply, IsIso.hom_inv_id, ModuleCat.id_apply]
  change (cohomologyMap (coindTrace (U : Subgroup G) A) 0).hom
    ((inv (shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0)).hom
      ((shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0).hom _)) = _
  rw [hinv, cohomologyMap_zero_H0Iso_inv]
  rfl

end CoresH0

section Projection

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : OpenSubgroup G)

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem coindTrace_naturality {k : Type} [CommRing k] [(U : Subgroup G).FiniteIndex]
    {A B : Rep.{0} k G} (φ : A ⟶ B) :
    Rep.coindMap (U : Subgroup G).subtype ((Rep.resFunctor (U : Subgroup G).subtype).map φ) ≫
        coindTrace (U : Subgroup G) B =
      coindTrace (U : Subgroup G) A ≫ φ := by
  ext f
  change (coindTrace (U : Subgroup G) B).hom
      ((Rep.coindMap (U : Subgroup G).subtype ((Rep.resFunctor (U : Subgroup G).subtype).map φ)).hom f) =
    φ.hom ((coindTrace (U : Subgroup G) A).hom f)
  rw [coindTrace_hom_apply, coindTrace_hom_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [coindTraceTerm_apply, coindTraceTerm_apply]
    change B.ρ x (φ.hom (f.1 x⁻¹)) = φ.hom (A.ρ x (f.1 x⁻¹))
    rw [Rep.hom_comm_apply]

theorem cohomologyMap_cohomologyCores {k : Type} [CommRing k] {A B : Rep.{0} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (φ : A ⟶ B) (n : ℕ) (x : cohomology (Rep.res (U : Subgroup G).subtype A) n) :
    (cohomologyMap φ n).hom ((cohomologyCores U A n).hom x) =
      (cohomologyCores U B n).hom
        ((cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n).hom x) := by
  have key : cohomologyCores U A n ≫ cohomologyMap φ n =
      cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n ≫ cohomologyCores U B n := by
    rw [cohomologyCores, cohomologyCores, Category.assoc, ← cohomologyMap_comp,
      ← coindTrace_naturality, cohomologyMap_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, shapiroMap_naturality]
  exact ConcreteCategory.congr_hom key x

theorem cohomologyCores_cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ)
    (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    (cohomologyCores U A 2).hom ((cupCharClassProf (Rep.res (U : Subgroup G).subtype A)
        (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _))).hom a) =
      (cupCharClassProf A χ).hom (invariantsNorm U A a) := by
  have hres : charClassProf (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _)) =
      (cohomologyRes (Rep.trivial ℤ G ℤ) (U : Subgroup G) 2).hom (charClassProf χ) :=
    (cohomologyMapAlong_charClassProf (U : Subgroup G).subtype (continuous_subgroup_subtype _) χ).symm
  have : IsDiscreteRep (Rep.res (U : Subgroup G).subtype (Rep.trivial ℤ G ℤ)) :=
    isDiscreteRep_res_subtype _ _
  have : IsDiscreteRep (Rep.res (U : Subgroup G).subtype A ⊗
      Rep.res (U : Subgroup G).subtype (Rep.trivial ℤ G ℤ)) := isDiscreteRep_tensor _ _
  have hρ : ∀ x : cohomology (Rep.res (U : Subgroup G).subtype A ⊗
      Rep.res (U : Subgroup G).subtype (Rep.trivial ℤ G ℤ)) 2,
      (cohomologyMap (ρ_ (Rep.res (U : Subgroup G).subtype A)).hom 2).hom x =
        (cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map (ρ_ A).hom) 2).hom
          ((cohomologyMap (resTensorIso (U : Subgroup G).subtype A (Rep.trivial ℤ G ℤ)).inv 2).hom x) :=
    fun x => ConcreteCategory.congr_hom (cohomologyMap_comp
      (resTensorIso (U : Subgroup G).subtype A (Rep.trivial ℤ G ℤ)).inv
      ((Rep.resFunctor (U : Subgroup G).subtype).map (ρ_ A).hom) 2) x
  change (cohomologyCores U A 2).hom ((cohomologyMap (ρ_ (Rep.res (U : Subgroup G).subtype A)).hom 2).hom
      (cup (zero_add 2) ((H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a)
        (charClassProf (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _))))) =
    (cohomologyMap (ρ_ A).hom 2).hom (cup (zero_add 2) ((H0Iso A).inv.hom (invariantsNorm U A a))
      (charClassProf χ))
  rw [hres]
  change (cohomologyCores U A 2).hom ((cohomologyMap (ρ_ (Rep.res (U : Subgroup G).subtype A)).hom 2).hom
      (cup (B := Rep.res (U : Subgroup G).subtype (Rep.trivial ℤ G ℤ)) (zero_add 2)
        ((H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a)
        ((cohomologyRes (Rep.trivial ℤ G ℤ) (U : Subgroup G) 2).hom (charClassProf χ)))) =
    (cohomologyMap (ρ_ A).hom 2).hom (cup (zero_add 2) ((H0Iso A).inv.hom (invariantsNorm U A a))
      (charClassProf χ))
  rw [hρ, ← cohomologyMap_cohomologyCores]
  have hp := cohomologyCores_cup_cohomologyRes U (A := A) (B := Rep.trivial ℤ G ℤ) (zero_add 2)
    ((H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a) (charClassProf χ)
  rw [cohomologyCores_H0Iso_inv] at hp
  exact congrArg (cohomologyMap (ρ_ A).hom 2).hom hp

end Projection

section Formation

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (C : Rep ℤ G)

def invariantsSubgroupOf {U V : OpenSubgroup G} (_h : V ≤ U)
    (a : (Rep.res (V : Subgroup G).subtype C).ρ.invariants) :
    (Rep.res (openSubgroupOf U V : Subgroup (U : Subgroup G)).subtype
      (Rep.res (U : Subgroup G).subtype C)).ρ.invariants :=
  ⟨a.1, fun w => a.2 ⟨w.1.1, w.2⟩⟩

noncomputable def invariantsNormLE {U V : OpenSubgroup G} (h : V ≤ U)
    (a : (Rep.res (V : Subgroup G).subtype C).ρ.invariants) :
    (Rep.res (U : Subgroup G).subtype C).ρ.invariants :=
  invariantsNorm (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) (invariantsSubgroupOf C h a)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
theorem coe_invariantsNormLE {U V : OpenSubgroup G} (h : V ≤ U)
    (a : (Rep.res (V : Subgroup G).subtype C).ρ.invariants) :
    (invariantsNormLE C h a : C) =
      ∑ c : (U : Subgroup G) ⧸ (openSubgroupOf U V : Subgroup (U : Subgroup G)), C.ρ c.out (a : C) :=
  coe_invariantsNorm _ _ _

variable [IsDiscreteRep C]

theorem ClassFormation.inv_cupCharClassProf_invariantsNormLE (F : ClassFormation C)
    (χ : Additive G →ₜ+ QZ) {U V : OpenSubgroup G} (h : V ≤ U)
    (a : (Rep.res (V : Subgroup G).subtype C).ρ.invariants) :
    F.inv U ((cupCharClassProf (Rep.res (U : Subgroup G).subtype C)
        (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _))).hom
          (invariantsNormLE C h a)) =
      F.inv V ((cupCharClassProf (Rep.res (V : Subgroup G).subtype C)
        (contCharComp χ (V : Subgroup G).subtype (continuous_subgroup_subtype _))).hom a) := by
  rw [← F.inv_cohomologyCoresLE h, cohomologyCoresLE_eq, ModuleCat.hom_comp, LinearMap.comp_apply,
    cohomologyMapAlong_cupCharClassProf _ _ _ _ a (invariantsSubgroupOf C h a) rfl]
  have hχ : contCharComp (contCharComp χ (V : Subgroup G).subtype (continuous_subgroup_subtype _))
      (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).toMonoidHom
        (continuous_subgroupOfEquivOfLe _) =
      contCharComp (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _))
        (openSubgroupOf U V : Subgroup (U : Subgroup G)).subtype (continuous_subgroup_subtype _) := by
    ext x
    rfl
  rw [hχ, cohomologyCores_cupCharClassProf]
  rfl

end Formation

end GroundTheory.ProfCoh
