import Mathlib
import GroundTheory.ProfiniteCohomology.PoincareDuality.Devissage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section MapAlongEquiv

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

theorem bijective_cohomologyMapAlong_of_mulEquiv (e : H ≃* G) (he : Continuous e.toMonoidHom)
    (he' : Continuous e.symm.toMonoidHom) {A : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A]
    [IsDiscreteRep B] (f : Rep.res e.toMonoidHom A ⟶ B) (g : Rep.res e.symm.toMonoidHom B ⟶ A)
    (hgf : ∀ a : A, g.hom (f.hom a) = a) (hfg : ∀ b : B, f.hom (g.hom b) = b) (n : ℕ) :
    Function.Bijective (cohomologyMapAlong e.toMonoidHom he f n).hom := by
  have h1 : cohomologyMapAlong e.toMonoidHom he f n ≫
      cohomologyMapAlong e.symm.toMonoidHom he' g n = 𝟙 _ := by
    rw [← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_eq_id _ _ (by ext x; simp) (fun a => hgf a) n
  have h2 : cohomologyMapAlong e.symm.toMonoidHom he' g n ≫
      cohomologyMapAlong e.toMonoidHom he f n = 𝟙 _ := by
    rw [← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_eq_id _ _ (by ext x; simp) (fun b => hfg b) n
  have e1 : ∀ x, (cohomologyMapAlong e.symm.toMonoidHom he' g n).hom
      ((cohomologyMapAlong e.toMonoidHom he f n).hom x) = x := fun x =>
    congrArg (fun φ => φ.hom x) h1
  have e2 : ∀ y, (cohomologyMapAlong e.toMonoidHom he f n).hom
      ((cohomologyMapAlong e.symm.toMonoidHom he' g n).hom y) = y := fun y =>
    congrArg (fun φ => φ.hom y) h2
  exact ⟨Function.LeftInverse.injective e1, Function.RightInverse.surjective e2⟩

end MapAlongEquiv

section OpenSubgroupOf

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in

theorem exists_eq_openSubgroupOf (U : OpenSubgroup G) (W : OpenSubgroup (U : Subgroup G)) :
    ∃ V : OpenSubgroup G, V ≤ U ∧ W = openSubgroupOf U V := by
  let V : OpenSubgroup G :=
    { toSubgroup := (W : Subgroup (U : Subgroup G)).map (U : Subgroup G).subtype
      isOpen' := by
        change IsOpen (Subtype.val '' (W : Set (U : Subgroup G)))
        exact U.isOpen.isOpenMap_subtype_val _ W.isOpen }
  refine ⟨V, fun x hx => ?_, ?_⟩
  · exact Subgroup.map_subtype_le (W : Subgroup (U : Subgroup G)) hx
  · apply OpenSubgroup.toSubgroup_injective
    change (W : Subgroup (U : Subgroup G)) =
      ((W : Subgroup (U : Subgroup G)).map (U : Subgroup G).subtype).subgroupOf U
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm

end OpenSubgroupOf

section Transport

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {n : ℕ} {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]

namespace DualityHypotheses

variable (H : DualityHypotheses n D)

abbrev fromSubgroupOf {U V : OpenSubgroup G} (hVU : V ≤ U) (C : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep C] (m : ℕ) :=
  cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom _ C) m

omit [CompactSpace G] in
theorem bijective_fromSubgroupOf {U V : OpenSubgroup G} (hVU : V ≤ U) (C : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep C] (m : ℕ) : Function.Bijective (fromSubgroupOf hVU C m).hom :=
  bijective_cohomologyMapAlong_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm
    (continuous_subgroupOfEquivOfLe_symm (show (V : Subgroup G) ≤ U from hVU))
    (continuous_subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU))
    (resSubgroupOfHom (show (V : Subgroup G) ≤ U from hVU) C)
    (resSubgroupOfInvHom (show (V : Subgroup G) ≤ U from hVU) C) (fun _ => rfl) (fun _ => rfl) m

include H in

theorem t_cohomologyCores_openSubgroupOf (U V : OpenSubgroup G) (hVU : V ≤ U)
    (z : cohomology (Rep.res (openSubgroupOf U V : Subgroup (U : Subgroup G)).subtype
      (Rep.res (U : Subgroup G).subtype D)) 2) :
    H.t U ((cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom z) =
      H.t V ((fromSubgroupOf hVU D 2).hom z) := by
  rw [← H.t_cores U V hVU, cohomologyCoresLE_eq]
  congr 1
  have h := congrArg (fun φ => φ.hom z)
    (cohomologyMapAlong_resSubgroupOfHom_comp (show (V : Subgroup G) ≤ U from hVU) D 2)
  change (cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom z =
    (cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom
      ((cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe
        (show (V : Subgroup G) ≤ U from hVU)).toMonoidHom (continuous_subgroupOfEquivOfLe _)
          (resSubgroupOfInvHom _ D) 2).hom ((fromSubgroupOf hVU D 2).hom z))
  congr 1
  exact h.symm

include H in

theorem bijective_t_cohomologyCores_openSubgroupOf (U V : OpenSubgroup G) (hVU : V ≤ U) :
    Function.Bijective ((H.t U).toAddMonoidHom.comp
      (cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom.toAddMonoidHom) := by
  have hfun : ⇑((H.t U).toAddMonoidHom.comp
      (cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom.toAddMonoidHom) =
      (H.t V) ∘ (fromSubgroupOf hVU D 2).hom := by
    funext z
    exact H.t_cohomologyCores_openSubgroupOf U V hVU z
  rw [hfun]
  exact (H.t V).bijective.comp (bijective_fromSubgroupOf hVU D 2)

end DualityHypotheses

end Transport

section Perfect

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {n : ℕ} {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]

namespace DualityHypotheses

variable (H : DualityHypotheses n D)

omit [IsTopologicalGroup G] [CompactSpace G] [IsDiscreteRep D] in
variable (n) in

def zmodSubgroupOfHom {U V : OpenSubgroup G} (hVU : V ≤ U) :
    Rep.res (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm.toMonoidHom
      (zmodRep.{u} ((V : Subgroup G).subgroupOf U) n) ⟶ zmodRep.{u} (V : Subgroup G) n :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [IsTopologicalGroup G] [CompactSpace G] [IsDiscreteRep D] in
variable (n) in

def zmodSubgroupOfInvHom {U V : OpenSubgroup G} (hVU : V ≤ U) :
    Rep.res (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).toMonoidHom
      (zmodRep.{u} (V : Subgroup G) n) ⟶ zmodRep.{u} ((V : Subgroup G).subgroupOf U) n :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [CompactSpace G] [IsDiscreteRep D] in
theorem bijective_zmodFromSubgroupOf {U V : OpenSubgroup G} (hVU : V ≤ U) (m : ℕ) :
    Function.Bijective (cohomologyMapAlong
      (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm.toMonoidHom
      (continuous_subgroupOfEquivOfLe_symm _) (zmodSubgroupOfHom n hVU) m).hom :=
  bijective_cohomologyMapAlong_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm
    (continuous_subgroupOfEquivOfLe_symm (show (V : Subgroup G) ≤ U from hVU))
    (continuous_subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU))
    (zmodSubgroupOfHom n hVU) (zmodSubgroupOfInvHom n hVU) (fun _ => rfl) (fun _ => rfl) m

omit [IsTopologicalGroup G] [CompactSpace G] [IsDiscreteRep D] in

theorem resFunctor_map_zmodMulPairing_comp {U V : OpenSubgroup G} (hVU : V ≤ U)
    (hD : ∀ d : D, n • d = 0) :
    (Rep.resFunctor (Subgroup.subgroupOfEquivOfLe
        (show (V : Subgroup G) ≤ U from hVU)).symm.toMonoidHom).map
        (zmodMulPairing n (Rep.res ((V : Subgroup G).subgroupOf U).subtype
          (Rep.res (U : Subgroup G).subtype D)) hD) ≫
        resSubgroupOfHom (show (V : Subgroup G) ≤ U from hVU) D =
      resTensorHom (Subgroup.subgroupOfEquivOfLe
          (show (V : Subgroup G) ≤ U from hVU)).symm.toMonoidHom
          (zmodSubgroupOfHom n hVU) (resSubgroupOfHom (show (V : Subgroup G) ≤ U from hVU) D) ≫
        zmodMulPairing n (Rep.res (V : Subgroup G).subtype D) hD := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a d => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [CompactSpace G] in

theorem fromSubgroupOf_cupPairing {U V : OpenSubgroup G} (hVU : V ≤ U) (hD : ∀ d : D, n • d = 0)
    (a : cohomology (zmodRep.{u} ((V : Subgroup G).subgroupOf U) n) 1)
    (b : cohomology (Rep.res ((V : Subgroup G).subgroupOf U).subtype
      (Rep.res (U : Subgroup G).subtype D)) 1) :
    fromSubgroupOf hVU D 2 (cupPairing (zmodMulPairing n (Rep.res ((V : Subgroup G).subgroupOf U).subtype
        (Rep.res (U : Subgroup G).subtype D)) hD) (show 1 + 1 = 2 from rfl) a b) =
      cupPairing (zmodMulPairing n (Rep.res (V : Subgroup G).subtype D) hD) (show 1 + 1 = 2 from rfl)
        (cohomologyMapAlong
          (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm.toMonoidHom
          (continuous_subgroupOfEquivOfLe_symm _) (zmodSubgroupOfHom n hVU) 1 a)
        (fromSubgroupOf hVU D 1 b) := by
  rw [cupPairing_apply, cupPairing_apply, cohomologyMapAlong_cohomologyMap,
    resFunctor_map_zmodMulPairing_comp hVU hD, ← cohomologyMap_cohomologyMapAlong,
    cohomologyMapAlong_resTensorHom_cup]

include H in

theorem isPerfectPairing_openSubgroupOf (U V : OpenSubgroup G) (hVU : V ≤ U) :
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n (Rep.res (openSubgroupOf U V :
        Subgroup (U : Subgroup G)).subtype (Rep.res (U : Subgroup G).subtype D))
        (nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv)) (show 1 + 1 = 2 from rfl)))
      ((H.t U).toAddMonoidHom.comp (cohomologyCores (openSubgroupOf U V)
        (Rep.res (U : Subgroup G).subtype D) 2).hom.toAddMonoidHom) := by
  obtain ⟨P₁, P₂⟩ := H.isPerfectPairing V
  have hD := nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv
  have key : ∀ a b, (H.t U) ((cohomologyCores (openSubgroupOf U V)
      (Rep.res (U : Subgroup G).subtype D) 2).hom
        (cupPairing (zmodMulPairing n (Rep.res ((V : Subgroup G).subgroupOf U).subtype
          (Rep.res (U : Subgroup G).subtype D)) hD) (show 1 + 1 = 2 from rfl) a b)) =
      H.t V (cupPairing (zmodMulPairing n (Rep.res (V : Subgroup G).subtype D) hD)
        (show 1 + 1 = 2 from rfl)
        ((cohomologyMapAlong
          (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm.toMonoidHom
          (continuous_subgroupOfEquivOfLe_symm _) (zmodSubgroupOfHom n hVU) 1).hom a)
        ((fromSubgroupOf hVU D 1).hom b)) := by
    intro a b
    rw [H.t_cohomologyCores_openSubgroupOf U V hVU]
    exact congrArg (H.t V) (fromSubgroupOf_cupPairing hVU hD a b)
  constructor
  · exact bijective_of_bijective_comp P₁ (bijective_zmodFromSubgroupOf hVU 1)
      (γ := (fromSubgroupOf hVU D 1).hom.toAddMonoidHom) (bijective_fromSubgroupOf hVU D 1)
      (fun a b => key a b)
  · exact bijective_of_bijective_comp P₂ (bijective_fromSubgroupOf hVU D 1)
      (γ := (cohomologyMapAlong
          (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm.toMonoidHom
          (continuous_subgroupOfEquivOfLe_symm _) (zmodSubgroupOfHom n hVU) 1).hom.toAddMonoidHom)
      (bijective_zmodFromSubgroupOf hVU 1) (fun b a => key a b)

include H in

theorem groupDualityHypotheses (U : OpenSubgroup G) :
    GroupDualityHypotheses n (Rep.res (U : Subgroup G).subtype D) (H.t U).toAddMonoidHom where
  nonempty_addEquiv := H.nonempty_addEquiv
  finite_two M _ _ hM := H.finite_cohomology U M hM 2 le_rfl
  subsingleton_three M _ _ hM := H.subsingleton_cohomology_three U M hM
  bijective_cores W := by
    obtain ⟨V, hVU, rfl⟩ := exists_eq_openSubgroupOf U W
    exact H.bijective_t_cohomologyCores_openSubgroupOf U V hVU
  isPerfectPairing W := by
    obtain ⟨V, hVU, rfl⟩ := exists_eq_openSubgroupOf U W
    exact H.isPerfectPairing_openSubgroupOf U V hVU

end DualityHypotheses

end Perfect

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]

namespace DualityHypotheses

variable (H : DualityHypotheses n D)

instance isDiscreteRep_dualRep_res (S : Subgroup G) (M : Rep.{u} (ULift.{u} ℤ) S) [IsDiscreteRep M]
    [Finite M] : IsDiscreteRep (dualRep (Rep.res S.subtype D) M) :=
  isDiscreteRep_dualRep _ _

include H in

theorem bijective_dualityMap (U : OpenSubgroup G) (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G))
    [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective
      (dualityMap (Rep.res (U : Subgroup G).subtype D) h (H.t U).toAddMonoidHom M) :=
  (H.groupDualityHypotheses U).bijective_dualityMap M hM h

end DualityHypotheses

end Main

section Top

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def topOpenSubgroupEquiv : ((⊤ : OpenSubgroup G) : Subgroup G) ≃* G where
  toFun x := x
  invFun x := ⟨x, Subgroup.mem_top x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [IsTopologicalGroup G] in
theorem continuous_topOpenSubgroupEquiv :
    Continuous (topOpenSubgroupEquiv (G := G)).toMonoidHom :=
  continuous_subtype_val

omit [IsTopologicalGroup G] in
theorem continuous_topOpenSubgroupEquiv_symm :
    Continuous (topOpenSubgroupEquiv (G := G)).symm.toMonoidHom :=
  continuous_id.subtype_mk _

theorem bijective_cohomologyRes_top {k : Type u} [CommRing k] (A : Rep.{u} k G) [IsDiscreteRep A]
    (m : ℕ) : Function.Bijective (cohomologyRes A ((⊤ : OpenSubgroup G) : Subgroup G) m).hom :=
  bijective_cohomologyMapAlong_of_mulEquiv (A := A)
    (B := Rep.res ((⊤ : OpenSubgroup G) : Subgroup G).subtype A) topOpenSubgroupEquiv
    continuous_topOpenSubgroupEquiv continuous_topOpenSubgroupEquiv_symm (𝟙 _)
    (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩) (fun _ => rfl) (fun _ => rfl) m

end Top

section Group

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {n : ℕ} {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [IsDiscreteRep D] in

theorem resTensorIso_inv_comp_resFunctor_map_evalPairing (S : Subgroup G)
    (M : Rep.{u} (ULift.{u} ℤ) G) :
    (resTensorIso S.subtype M (dualRep D M)).inv ≫ (Rep.resFunctor S.subtype).map (evalPairing D M) =
      evalPairing (Rep.res S.subtype D) (Rep.res S.subtype M) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

namespace DualityHypotheses

variable (H : DualityHypotheses n D)

def tTop : cohomology D 2 →+ ZMod n :=
  (H.t ⊤).toAddMonoidHom.comp
    (cohomologyRes D ((⊤ : OpenSubgroup G) : Subgroup G) 2).hom.toAddMonoidHom

variable [NeZero n]

include H in

theorem bijective_dualityMap_of_group (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective (dualityMap D h H.tTop M) := by
  have : Finite (Rep.res ((⊤ : OpenSubgroup G) : Subgroup G).subtype M) := inferInstanceAs (Finite M)
  have hU := H.bijective_dualityMap ⊤ (Rep.res ((⊤ : OpenSubgroup G) : Subgroup G).subtype M)
    hM h
  refine bijective_of_bijective_comp hU (bijective_cohomologyRes_top M r)
    (γ := (cohomologyRes (dualRep D M) ((⊤ : OpenSubgroup G) : Subgroup G) s).hom.toAddMonoidHom)
    (bijective_cohomologyRes_top (dualRep D M) s) fun x y => ?_
  rw [dualityMap_apply, dualityMap_apply]
  change (H.t ⊤) (cohomologyRes D ((⊤ : OpenSubgroup G) : Subgroup G) 2
    (cupPairing (evalPairing D M) h x y)) = _
  rw [cohomologyRes_cupPairing, resTensorIso_inv_comp_resFunctor_map_evalPairing]
  rfl

end DualityHypotheses

end Group

end GroundTheory.ProfCoh
