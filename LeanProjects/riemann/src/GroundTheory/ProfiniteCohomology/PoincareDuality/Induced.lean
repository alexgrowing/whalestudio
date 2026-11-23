import Mathlib
import GroundTheory.ProfiniteCohomology.PoincareDuality.InducedDual
import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
import GroundTheory.ProfiniteCohomology.CupProducts.CohomologyMapRightUnitorCupUnitClass
import GroundTheory.ProfiniteCohomology.Characters
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section Finite

variable {k Γ : Type u} [CommRing k] [Group Γ] (W : Subgroup Γ) (V : Type u) [AddCommGroup V]
  [Module k V]

instance finite_coind_trivial [Finite V] [W.FiniteIndex] :
    Finite (Rep.coind W.subtype (Rep.trivial k W V)) := by
  refine Finite.of_injective (fun f : Rep.coind W.subtype (Rep.trivial k W V) =>
    fun c : Γ ⧸ W => f.1 c.out⁻¹) fun f f' hff' => Subtype.ext (funext fun x => ?_)
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W x⁻¹
  have h := congrFun hff' ((x⁻¹ : Γ) : Γ ⧸ W)
  simp only at h
  rw [hw, mul_inv_rev, inv_inv] at h
  rwa [← Subgroup.coe_inv, coind_trivial_apply_mul W V f w⁻¹ x,
    coind_trivial_apply_mul W V f' w⁻¹ x] at h

end Finite

section Formula

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] (W : OpenSubgroup Γ) (V : Type u) [AddCommGroup V] [Module k V] [Finite V]
  (D : Rep.{u} k Γ) [IsDiscreteRep D]

instance isDiscreteRep_coind_trivial :
    IsDiscreteRep (Rep.coind (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V)) :=
  isDiscreteRep_coind W _

instance isDiscreteRep_dualRep_res_trivial :
    IsDiscreteRep (dualRep (Rep.res (W : Subgroup Γ).subtype D) (Rep.trivial k (W : Subgroup Γ) V)) :=
  isDiscreteRep_dualRep _ _

instance isDiscreteRep_coind_dualRep_res_trivial :
    IsDiscreteRep (Rep.coind (W : Subgroup Γ).subtype
      (dualRep (Rep.res (W : Subgroup Γ).subtype D) (Rep.trivial k (W : Subgroup Γ) V))) :=
  isDiscreteRep_coind W _

instance isDiscreteRep_dualRep_coind_trivial :
    IsDiscreteRep (dualRep D (Rep.coind (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V))) :=
  isDiscreteRep_dualRep _ _

theorem cupPairing_evalPairing_coindDualHom {r s m : ℕ} (h : r + s = m)
    (x : cohomology (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V)) r)
    (y : cohomology (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype
      (dualRep (Rep.res (W : Subgroup Γ).subtype D) (Rep.trivial k (W : Subgroup Γ) V))) s) :
    cupPairing (evalPairing D (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V))) h x (cohomologyMap (coindDualHom (W : Subgroup Γ) V D) s y) =
      cohomologyCores W D m (cupPairing (evalPairing (Rep.res (W : Subgroup Γ).subtype D)
        (Rep.trivial k (W : Subgroup Γ) V)) h (shapiroMap W (Rep.trivial k (W : Subgroup Γ) V) r x)
        (shapiroMap W (dualRep (Rep.res (W : Subgroup Γ).subtype D) (Rep.trivial k (W : Subgroup Γ) V)) s y)) := by
  have e1 := cupPairing_cohomologyMap
    (evalPairing D (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V))) (𝟙 _) (coindDualHom (W : Subgroup Γ) V D)
    h x y
  rw [cohomologyMap_id] at e1
  change cupPairing (evalPairing D (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V))) h x (cohomologyMap (coindDualHom (W : Subgroup Γ) V D) s y) =
    _ at e1
  rw [e1, tensorHom_coindDualHom_evalPairing, ← cohomologyMap_cupPairing,
    ← cohomologyCores_shapiroMap]
  congr 1
  rw [cupPairing_apply, cupPairing_apply, shapiroMap_eq, shapiroMap_eq, shapiroMap_eq,
    ← cohomologyMapAlong_resTensorHom_cup, cohomologyMap_cohomologyMapAlong,
    cohomologyMapAlong_cohomologyMap, res_coindDualPairing_comp_coindEvalOne]

end Formula

section Unit

variable {k H : Type u} [CommRing k] [Group H]

def unitHom (A : Rep.{u} k H) (a : A) (ha : ∀ g : H, A.ρ g a = a) : 𝟙_ (Rep.{u} k H) ⟶ A :=
  Rep.ofHom ⟨LinearMap.toSpanSingleton k A a, fun g => LinearMap.ext fun c => by
    change (c • a : A) = A.ρ g (c • a)
    rw [map_smul, ha]⟩

theorem unitHom_hom_apply (A : Rep.{u} k H) (a : A) (ha : ∀ g : H, A.ρ g a = a) (c : k) :
    (unitHom A a ha).hom c = c • a :=
  rfl

end Unit

section H0

theorem zmodRep_ρ_apply {H : Type u} [Monoid H] {n : ℕ} (g : H) (v : zmodRep.{u} H n) :
    (zmodRep.{u} H n).ρ g v = v :=
  rfl

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ}

def zmodH0Class (a : ZMod n) : cohomology (zmodRep.{u} H n) 0 :=
  cohomologyMap (unitHom (zmodRep.{u} H n) (ULift.up a) fun g => zmodRep_ρ_apply g _) 0 unitClass

theorem zmodH0Class_surjective : Function.Surjective (zmodH0Class (H := H) (n := n)) := by
  intro x
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 0 x
  refine ⟨(cochainOf _ (cocycleι _ 0 z) (fun i => i.elim0)).down, ?_⟩
  rw [zmodH0Class, unitClass, cohomologyMap_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_unitCocycle]
  funext σ
  have hσ : σ = fun i => i.elim0 := Subsingleton.elim _ _
  rw [hσ]
  exact one_smul _ _

variable [NeZero n] (D' : Rep.{u} (ULift.{u} ℤ) H) [IsDiscreteRep D'] (hD : ∀ d : D', n • d = 0)

omit [TopologicalSpace H] [IsTopologicalGroup H] [IsDiscreteRep D'] in

theorem unitHom_tensorHom_zmodMulPairing (a : ZMod n) :
    (unitHom (zmodRep.{u} H n) (ULift.up a) (fun g => zmodRep_ρ_apply g _) ⊗ₘ 𝟙 D') ≫ zmodMulPairing n D' hD =
      (λ_ D').hom ≫ (a.val • 𝟙 D') := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext
    (TensorProduct.ext' fun (c : ULift.{u} ℤ) d => ?_))
  change (zmodMulPairing n D' hD).hom
      ((unitHom (zmodRep.{u} H n) (ULift.up a) fun g => zmodRep_ρ_apply g _).hom c ⊗ₜ[ULift.{u} ℤ]
        d) =
    (a.val • 𝟙 D').hom ((λ_ D').hom.hom (c ⊗ₜ[ULift.{u} ℤ] d))
  rw [unitHom_hom_apply, ← TensorProduct.smul_tmul']
  change (zmodMulPairing n D' hD).hom.toLinearMap (_ • _) = _
  rw [LinearMap.map_smul, Representation.IntertwiningMap.toLinearMap_apply, zmodMulPairing_tmul,
    GroundTheory.GroupCoh.leftUnitor_hom_tmul, Rep.nsmul_hom, Representation.IntertwiningMap.coe_nsmul,
    Pi.smul_apply, ZMod.cast_eq_val, natCast_zsmul, smul_comm]
  rfl

theorem cupPairing_zmodH0Class (h : 0 + 2 = 2) (a : ZMod n) (y : cohomology D' 2) :
    cupPairing (zmodMulPairing n D' hD) h (zmodH0Class a) y = a.val • y := by
  have e := cupPairing_cohomologyMap (zmodMulPairing n D' hD)
    (unitHom (zmodRep.{u} H n) (ULift.up a) fun g => zmodRep_ρ_apply g _) (𝟙 D') h unitClass y
  rw [cohomologyMap_id] at e
  change cupPairing (zmodMulPairing n D' hD) h (zmodH0Class a) y = _ at e
  rw [e, unitHom_tensorHom_zmodMulPairing, ← cohomologyMap_cupPairing, cupPairing_apply,
    cohomologyMap_leftUnitor_unitClass_cup, cohomologyMap_nsmul_id]
  rfl

theorem bijective_zmodMulPairing_zero (T : cohomology D' 2 →+ ZMod n)
    (hT : Function.Bijective T) (h : 0 + 2 = 2) :
    Function.Bijective (fun x : cohomology (zmodRep.{u} H n) 0 =>
      T.comp (bilinAddHom (cupPairing (zmodMulPairing n D' hD) h) x)) := by
  obtain ⟨y₀, hy₀⟩ := hT.2 1
  have hF : ∀ (a : ZMod n) (y : cohomology D' 2),
      T.comp (bilinAddHom (cupPairing (zmodMulPairing n D' hD) h) (zmodH0Class a)) y =
        a.val • T y := by
    intro a y
    rw [AddMonoidHom.comp_apply, bilinAddHom_apply, cupPairing_zmodH0Class, map_nsmul]
  constructor
  · intro x x' hxx'
    obtain ⟨a, rfl⟩ := zmodH0Class_surjective x
    obtain ⟨a', rfl⟩ := zmodH0Class_surjective x'
    have key := DFunLike.congr_fun hxx' y₀
    beta_reduce at key
    rw [hF, hF, hy₀, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at key
    rw [key]
  · intro χ
    refine ⟨zmodH0Class (χ y₀), AddMonoidHom.ext fun y => ?_⟩
    beta_reduce
    rw [hF]
    have hy : y = (T y).val • y₀ :=
      hT.1 (by rw [map_nsmul, hy₀, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val])
    conv_rhs => rw [hy]
    rw [map_nsmul, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      mul_comm]

end H0

section Transfer

variable {n : ℕ}

theorem bijective_of_bijective_comp {X X' Y Y' : Type*} [AddCommGroup Y] [AddCommGroup Y']
    {F : X → (Y →+ ZMod n)} (hF : Function.Bijective F) {α : X' → X} (hα : Function.Bijective α)
    {γ : Y' →+ Y} (hγ : Function.Bijective γ) {F' : X' → (Y' →+ ZMod n)}
    (hF' : ∀ x' y', F' x' y' = F (α x') (γ y')) : Function.Bijective F' := by
  let e := AddEquiv.ofBijective γ hγ
  have hP : Function.Bijective (fun χ : Y →+ ZMod n => χ.comp γ) := by
    refine ⟨fun χ χ' hχ => AddMonoidHom.ext fun y => ?_, fun ψ =>
      ⟨ψ.comp e.symm.toAddMonoidHom, AddMonoidHom.ext fun y' => ?_⟩⟩
    · obtain ⟨y', rfl⟩ := hγ.2 y
      exact DFunLike.congr_fun hχ y'
    · change ψ (e.symm (γ y')) = ψ y'
      rw [show γ y' = e y' from rfl, AddEquiv.symm_apply_apply]
  have hcomp : F' = (fun χ : Y →+ ZMod n => χ.comp γ) ∘ F ∘ α :=
    funext fun x' => AddMonoidHom.ext fun y' => hF' x' y'
  rw [hcomp]
  exact hP.comp (hF.comp hα)

end Transfer

section Main

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem bijective_cohomologyMap_of_comp_eq_id {A B : Rep.{u} k Γ} [IsDiscreteRep A]
    [IsDiscreteRep B] (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 B) (m : ℕ) :
    Function.Bijective (cohomologyMap f m) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cohomologyMap g m, fun x => ?_, fun y => ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← cohomologyMap_comp, hfg, cohomologyMap_id]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← cohomologyMap_comp, hgf, cohomologyMap_id]
    rfl

variable [CompactSpace Γ] {n : ℕ} [NeZero n]

instance (priority := high) finite_uliftZMod : Finite (ULift.{u} (ZMod n)) :=
  Finite.of_equiv _ Equiv.ulift.symm

instance finite_coind_zmodRep (W : OpenSubgroup Γ) :
    Finite (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) :=
  finite_coind_trivial _ _

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [NeZero n] in

theorem nsmul_coind_zmodRep_eq_zero (W : OpenSubgroup Γ)
    (f : Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) : n • f = 0 :=
  Subtype.ext (funext fun x => nsmul_zmodRep_eq_zero (W : Subgroup Γ) n (f.1 x))

instance isDiscreteRep_coind_zmodRep (W : OpenSubgroup Γ) :
    IsDiscreteRep (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) :=
  isDiscreteRep_coind W _

instance isDiscreteRep_dualRep_coind_zmodRep (D : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep D]
    (W : OpenSubgroup Γ) :
    IsDiscreteRep (dualRep D (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n))) :=
  isDiscreteRep_dualRep _ _

theorem bijective_dualityMap_coind (D : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep D]
    (hD : Nonempty (D ≃+ ZMod n)) (t : cohomology D 2 →+ ZMod n) (W : OpenSubgroup Γ)
    (hT : Function.Bijective (t.comp (cohomologyCores W D 2).hom.toAddMonoidHom))
    (hP : IsPerfectPairing (bilinAddHom (cupPairing (zmodMulPairing n
      (Rep.res (W : Subgroup Γ).subtype D) (nsmul_eq_zero_of_nonempty_addEquiv hD))
      (show 1 + 1 = 2 from rfl))) (t.comp (cohomologyCores W D 2).hom.toAddMonoidHom))
    {r s : ℕ} (h : r + s = 2) (hr : r ≤ 1) :
    Function.Bijective (dualityMap D h t
      (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n))) := by
  have hD' : ∀ d : Rep.res (W : Subgroup Γ).subtype D, n • d = 0 :=
    nsmul_eq_zero_of_nonempty_addEquiv hD
  have hΨ : Function.Bijective (cohomologyMap (coindDualInv (W : Subgroup Γ)
      (ULift.{u} (ZMod n)) D) s) :=
    bijective_cohomologyMap_of_comp_eq_id _ _ (coindDualInv_comp_coindDualHom _ _ _)
      (coindDualHom_comp_coindDualInv _ _ _) s
  have hsh : ∀ (B : Rep.{u} (ULift.{u} ℤ) (W : Subgroup Γ)) [IsDiscreteRep B] (m : ℕ),
      Function.Bijective (shapiroMap W B m) := fun B _ m =>
    Function.bijective_iff_has_inverse.2 ⟨inv (shapiroMap W B m), inv_shapiroMap_apply W m,
      shapiroMap_inv_apply W m⟩
  have he : Function.Bijective (cohomologyMap
      (zmodDualIso n (Rep.res (W : Subgroup Γ).subtype D) hD').hom s) :=
    bijective_cohomologyMap_of_comp_eq_id _ _ (Iso.hom_inv_id _) (Iso.inv_hom_id _) s
  let γ : cohomology (dualRep D (Rep.coind (W : Subgroup Γ).subtype
      (zmodRep.{u} (W : Subgroup Γ) n))) s →+ cohomology (Rep.res (W : Subgroup Γ).subtype D) s :=
    ((cohomologyMap (zmodDualIso n (Rep.res (W : Subgroup Γ).subtype D) hD').hom s).hom.comp
      ((shapiroMap W _ s).hom.comp (cohomologyMap (coindDualInv (W : Subgroup Γ)
        (ULift.{u} (ZMod n)) D) s).hom)).toAddMonoidHom
  have hγ : Function.Bijective γ := he.comp ((hsh _ s).comp hΨ)
  have key : ∀ x y, dualityMap D h t
      (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) x y =
      t.comp (cohomologyCores W D 2).hom.toAddMonoidHom
        (cupPairing (zmodMulPairing n (Rep.res (W : Subgroup Γ).subtype D) hD') h
          (shapiroMap W _ r x) (γ y)) := by
    intro x y
    have hy : cohomologyMap (coindDualHom (W : Subgroup Γ) (ULift.{u} (ZMod n)) D) s
        (cohomologyMap (coindDualInv (W : Subgroup Γ) (ULift.{u} (ZMod n)) D) s y) = y := by
      rw [← ConcreteCategory.comp_apply, ← cohomologyMap_comp, coindDualInv_comp_coindDualHom,
        cohomologyMap_id]
      rfl
    rw [dualityMap_apply]
    conv_lhs => rw [← hy]
    rw [cupPairing_evalPairing_coindDualHom]
    have e2 := cupPairing_cohomologyMap (zmodMulPairing n (Rep.res (W : Subgroup Γ).subtype D) hD')
      (𝟙 _) (zmodDualIso n (Rep.res (W : Subgroup Γ).subtype D) hD').hom h
      (shapiroMap W _ r x) (shapiroMap W _ s
        (cohomologyMap (coindDualInv (W : Subgroup Γ) (ULift.{u} (ZMod n)) D) s y))
    rw [cohomologyMap_id, tensorHom_zmodDualIso_zmodMulPairing] at e2
    change t (cohomologyCores W D 2 _) = t (cohomologyCores W D 2 _)
    congr 2
    exact e2.symm
  obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
  · obtain rfl : s = 2 := by omega
    exact bijective_of_bijective_comp
      (bijective_zmodMulPairing_zero (Rep.res (W : Subgroup Γ).subtype D) hD' _ hT h)
      (hsh _ 0) hγ key
  · obtain rfl : s = 1 := by omega
    exact bijective_of_bijective_comp hP.1 (hsh _ 1) hγ key

end Main

end GroundTheory.ProfCoh
