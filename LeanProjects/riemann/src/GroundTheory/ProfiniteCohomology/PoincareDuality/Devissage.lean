import Mathlib
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
import GroundTheory.ProfiniteCohomology.PoincareDuality.Induced
import GroundTheory.ProfiniteCohomology.PoincareDuality.CupPairingEvalPairingCohomologyMap
import GroundTheory.ProfiniteCohomology.PoincareDuality.DeltaPairing
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.Characters
import GroundTheory.ProfiniteCohomology.CupProducts.Graded
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

universe u

attribute [local instance 2000] Rep.hV2

section Helpers

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem injective_cohomologyMap_zero {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (f : A ⟶ B) (hf : Function.Injective f.hom) : Function.Injective (cohomologyMap f 0).hom := by
  intro x y hxy
  have e := fun z => congrArg (fun φ => φ.hom z) (cohomologyMap_zero_comp_H0Iso_hom f)
  have hx := e x
  have hy := e y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx hy
  have h : ((Rep.invariantsFunctor k G).map f).hom ((H0Iso A).hom.hom x) =
      ((Rep.invariantsFunctor k G).map f).hom ((H0Iso A).hom.hom y) := by
    rw [← hx, ← hy, hxy]
  have h' : (H0Iso A).hom.hom x = (H0Iso A).hom.hom y :=
    Subtype.ext (hf (congrArg Subtype.val h))
  rw [← H0Iso_inv_hom_apply A x, ← H0Iso_inv_hom_apply A y, h']

end Helpers

section Naturality

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D] {n : ℕ} {t : cohomology D 2 →+ ZMod n}

theorem dualityMap_δ {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]
    (hS : S.ShortExact) (hT : (dualShortComplex D S).ShortExact) (x : cohomology S.X₃ 0)
    (y : cohomology (dualRep D S.X₁) 1) :
    dualityMap D (rfl : 1 + 1 = 2) t S.X₁ ((δ hS 0 1 rfl).hom x) y =
      -dualityMap D (rfl : 0 + 2 = 2) t S.X₃ x ((δ hT 1 2 rfl).hom y) := by
  rw [dualityMap_apply, dualityMap_apply, ← map_neg]
  congr 1
  have := cupPairing_δ_eq (S := S) (T := dualShortComplex D S) (p := 0) (p' := 1) (q := 1)
    (q' := 2) (n := 2) (evalPairing D S.X₁) (evalPairing D S.X₂) (evalPairing D S.X₃)
    (tensorHom_evalPairing D S.f) (tensorHom_evalPairing D S.g).symm hS hT rfl rfl rfl rfl x y
  have h1 : ((-1 : ULift.{u} ℤ) ^ (0 + 1)) = -1 := by norm_num
  rw [h1, neg_one_smul] at this
  exact this

end Naturality

section Core

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

structure GroupDualityHypotheses (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep D]
    (t : cohomology D 2 →+ ZMod n) : Prop where
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  finite_two : ∀ (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Finite (cohomology M 2)
  subsingleton_three : ∀ (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (cohomology M 3)
  bijective_cores : ∀ W : OpenSubgroup Γ,
    Function.Bijective (t.comp (cohomologyCores W D 2).hom.toAddMonoidHom)
  isPerfectPairing : ∀ W : OpenSubgroup Γ,
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n (Rep.res (W : Subgroup Γ).subtype D)
        (nsmul_eq_zero_of_nonempty_addEquiv nonempty_addEquiv)) (show 1 + 1 = 2 from rfl)))
      (t.comp (cohomologyCores W D 2).hom.toAddMonoidHom)

namespace GroupDualityHypotheses

variable {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) Γ} [IsDiscreteRep D]
  {t : cohomology D 2 →+ ZMod n} (H : GroupDualityHypotheses n D t)

include H in
theorem finite_D : Finite D :=
  finite_of_nonempty_addEquiv H.nonempty_addEquiv

omit [NeZero n] in
include H in
theorem nsmul_D (d : D) : n • d = 0 :=
  nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv d

include H in

theorem exists_devissage (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    ∃ (I Q : Rep.{u} (ULift.{u} ℤ) Γ) (_ : IsDiscreteRep I) (_ : IsDiscreteRep Q) (_ : Finite I)
      (_ : Finite Q) (i : M ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ (∀ x : I, n • x = 0) ∧ (∀ x : Q, n • x = 0) ∧
      Function.Bijective (dualityMap D (rfl : 0 + 2 = 2) t I) ∧
      Function.Bijective (dualityMap D (rfl : 1 + 1 = 2) t I) := by
  obtain ⟨W, J, _, i, hi⟩ := exists_injective_biproduct_coind (n := n) M hM
  have hφ : ∀ {r s : ℕ} (h : r + s = 2), r ≤ 1 → Function.Bijective (dualityMap D h t
      (⨁ fun _ : J => Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n) :
        Rep.{u} (ULift.{u} ℤ) Γ)) :=
    fun h hr => bijective_dualityMap_biproduct D _ h t fun _ =>
      bijective_dualityMap_coind D H.nonempty_addEquiv t W (H.bijective_cores W)
        (H.isPerfectPairing W) h hr
  have hnI : ∀ x : ((⨁ fun _ : J => Rep.coind (W : Subgroup Γ).subtype
      (zmodRep.{u} (W : Subgroup Γ) n) : Rep.{u} (ULift.{u} ℤ) Γ) : Type u), n • x = 0 := by
    intro x
    rw [biproduct_eq_sum _ x, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← map_nsmul, nsmul_coind_zmodRep_eq_zero W, map_zero]
  have hmono : Mono i := (Rep.mono_iff_injective i).2 hi
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel i)) hmono
      (inferInstance : Epi (cokernel.π i))
  have hQd : IsDiscreteRep (cokernel i) := isDiscreteRep_X₃_of_shortExact hS
  have hsurj : Function.Surjective (cokernel.π i).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hQf : Finite ((cokernel i : Rep.{u} (ULift.{u} ℤ) Γ) : Type u) :=
    Finite.of_surjective _ hsurj
  refine ⟨_, cokernel i, inferInstance, hQd, inferInstance, hQf, i, cokernel.π i,
    cokernel.condition i, hS, hnI, fun x => ?_, hφ rfl (by norm_num), hφ rfl le_rfl⟩
  obtain ⟨y, rfl⟩ := hsurj x
  rw [← map_nsmul, hnI, map_zero]

end GroupDualityHypotheses

end Core

section Steps

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) Γ} [IsDiscreteRep D]
  {t : cohomology D 2 →+ ZMod n}

namespace GroupDualityHypotheses

variable (H : GroupDualityHypotheses n D t)

include H in

theorem injective_zero (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Injective (dualityMap D (rfl : 0 + 2 = 2) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI0, hI1⟩ := H.exists_devissage M hM
  have hi : Function.Injective i.hom := (Rep.mono_iff_injective i).1 hS.mono_f
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : dualityMap D (rfl : 0 + 2 = 2) t I ((cohomologyMap i 0).hom x) = 0 := by
    ext y
    rw [dualityMap_cohomologyMap D (rfl : 0 + 2 = 2) t i x y, hx]
    rfl
  have h2 : (cohomologyMap i 0).hom x = 0 := (injective_iff_map_eq_zero _).1 hI0.1 _ h1
  exact (injective_iff_map_eq_zero _).1 (injective_cohomologyMap_zero i hi) x h2

include H in

theorem surjective_zero (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Surjective (dualityMap D (rfl : 0 + 2 = 2) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI0, hI1⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  have hsurj : Function.Surjective (cohomologyMap (dualMap D i) 2).hom := by
    intro y
    have : Subsingleton (cohomology (dualRep D Q) 3) :=
      H.subsingleton_three (dualRep D Q) (nsmul_dualRep_eq_zero H.nsmul_D)
    exact (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hT 2 3 rfl) y
      (Subsingleton.elim _ _)
  intro l
  obtain ⟨v, hv⟩ := hI0.2 (l.comp (cohomologyMap (dualMap D i) 2).hom.toAddMonoidHom)
  have hpv : (cohomologyMap p 0).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_zero Q hnQ)
    ext y
    rw [dualityMap_cohomologyMap D (rfl : 0 + 2 = 2) t p v y, hv]
    change l ((cohomologyMap (dualMap D p) 2 ≫ cohomologyMap (dualMap D i) 2).hom y) = 0
    rw [← cohomologyMap_comp, ← dualMap_comp, w, dualMap_zero, cohomologyMap_zero]
    exact map_zero l
  obtain ⟨m, hm⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 0) v hpv
  refine ⟨m, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := hsurj y
  rw [← dualityMap_cohomologyMap D (rfl : 0 + 2 = 2) t i m z]
  change dualityMap D (rfl : 0 + 2 = 2) t I ((cohomologyMap S.f 0).hom m) z = _
  rw [hm, hv]
  rfl

include H in
theorem bijective_zero (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (dualityMap D (rfl : 0 + 2 = 2) t M) :=
  ⟨H.injective_zero M hM, H.surjective_zero M hM⟩

include H in

theorem injective_one (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Injective (dualityMap D (rfl : 1 + 1 = 2) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI0, hI1⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : dualityMap D (rfl : 1 + 1 = 2) t I ((cohomologyMap i 1).hom x) = 0 := by
    ext y
    rw [dualityMap_cohomologyMap D (rfl : 1 + 1 = 2) t i x y, hx]
    rfl
  have hix : (cohomologyMap i 1).hom x = 0 := (injective_iff_map_eq_zero _).1 hI1.1 _ h1
  obtain ⟨q, hq⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS 0 1 rfl) x hix
  have hker : ((cohomologyMap (dualMap D p) 2).hom.toAddMonoidHom).ker ≤
      (dualityMap D (rfl : 0 + 2 = 2) t Q q).ker := by
    intro z hz
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hT 1 2 rfl) z hz
    rw [AddMonoidHom.mem_ker]
    rw [← hy]
    have e := dualityMap_δ (t := t) hS hT q y
    change dualityMap D (rfl : 1 + 1 = 2) t M ((δ hS 0 1 rfl).hom q) y = _ at e
    rw [hq, hx] at e
    exact neg_eq_zero.1 e.symm
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_cohomology_eq_zero _ (nsmul_dualRep_eq_zero H.nsmul_D) 2) _ _ hker
  obtain ⟨v, hv⟩ := hI0.2 ψ
  have hpv : (cohomologyMap p 0).hom v = q := by
    apply H.injective_zero Q hnQ
    ext z
    rw [dualityMap_cohomologyMap D (rfl : 0 + 2 = 2) t p v z, hv, ← hψ]
    rfl
  rw [← hq, ← hpv]
  exact congrArg (fun φ => φ.hom v) (comp_δ hS 0 1 rfl)

include H in

theorem surjective_one (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Surjective (dualityMap D (rfl : 1 + 1 = 2) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI0, hI1⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  intro l
  obtain ⟨v, hv⟩ := hI1.2 (l.comp (cohomologyMap (dualMap D i) 1).hom.toAddMonoidHom)
  have hpv : (cohomologyMap p 1).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_one Q hnQ)
    ext y
    rw [dualityMap_cohomologyMap D (rfl : 1 + 1 = 2) t p v y, hv]
    change l ((cohomologyMap (dualMap D p) 1 ≫ cohomologyMap (dualMap D i) 1).hom y) = 0
    rw [← cohomologyMap_comp, ← dualMap_comp, w, dualMap_zero, cohomologyMap_zero]
    exact map_zero l
  obtain ⟨x', hx'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 1) v hpv
  set ν := l - dualityMap D (rfl : 1 + 1 = 2) t M x' with hν
  have hker : ((δ hT 1 2 rfl).hom.toAddMonoidHom).ker ≤ ν.ker := by
    intro y hy
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hT 1 2 rfl) y hy
    rw [AddMonoidHom.mem_ker, ← hz, hν, AddMonoidHom.sub_apply, sub_eq_zero]
    change l ((cohomologyMap (dualMap D i) 1).hom z) =
      dualityMap D (rfl : 1 + 1 = 2) t M x' ((cohomologyMap (dualMap D i) 1).hom z)
    rw [← dualityMap_cohomologyMap D (rfl : 1 + 1 = 2) t i x' z]
    change _ = dualityMap D (rfl : 1 + 1 = 2) t I ((cohomologyMap S.f 1).hom x') z
    rw [hx', hv]
    rfl
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_cohomology_eq_zero _ (nsmul_dualRep_eq_zero H.nsmul_D) 2) _ _ hker
  obtain ⟨q, hq⟩ := (H.bijective_zero Q hnQ).2 ψ
  refine ⟨x' - (δ hS 0 1 rfl).hom q, ?_⟩
  ext y
  have e := dualityMap_δ (t := t) hS hT q y
  change dualityMap D (rfl : 1 + 1 = 2) t M ((δ hS 0 1 rfl).hom q) y = _ at e
  rw [map_sub, AddMonoidHom.sub_apply, e, hq, sub_neg_eq_add]
  have hψy : ψ ((δ hT 1 2 rfl).hom y) = ν y := congrArg (fun f => f y) hψ
  change _ + ψ ((δ hT 1 2 rfl).hom y) = l y
  rw [hψy, hν, AddMonoidHom.sub_apply, add_sub_cancel]

include H in
theorem bijective_one (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (dualityMap D (rfl : 1 + 1 = 2) t M) :=
  ⟨H.injective_one M hM, H.surjective_one M hM⟩

end GroupDualityHypotheses

end Steps

section Generic

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (D : Rep.{u} k Γ) [IsDiscreteRep D]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [IsDiscreteRep D] in

theorem tensorHom_toDualDual_evalPairing (M : Rep.{u} k Γ) :
    (𝟙 (dualRep D M) ⊗ₘ toDualDual D M) ≫ evalPairing D (dualRep D M) =
      (β_ (dualRep D M) M).hom ≫ evalPairing D M := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul f m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cupPairing_toDualDual (M : Rep.{u} k Γ) [IsDiscreteRep M] [IsDiscreteRep (dualRep D M)]
    [IsDiscreteRep (dualRep D (dualRep D M))] (x : cohomology M 2)
    (y : cohomology (dualRep D M) 0) :
    cupPairing (evalPairing D (dualRep D M)) (rfl : 0 + 2 = 2) y
        ((cohomologyMap (toDualDual D M) 2).hom x) =
      cupPairing (evalPairing D M) (rfl : 2 + 0 = 2) x y := by
  calc cupPairing (evalPairing D (dualRep D M)) (rfl : 0 + 2 = 2) y
        ((cohomologyMap (toDualDual D M) 2).hom x)
      = cupPairing (evalPairing D (dualRep D M)) (rfl : 0 + 2 = 2)
          (cohomologyMap (𝟙 (dualRep D M)) 0 y) (cohomologyMap (toDualDual D M) 2 x) := by
        rw [cohomologyMap_id]
        rfl
    _ = cupPairing ((𝟙 (dualRep D M) ⊗ₘ toDualDual D M) ≫ evalPairing D (dualRep D M))
          (rfl : 0 + 2 = 2) y x := cupPairing_cohomologyMap _ _ _ _ _ _
    _ = cupPairing ((β_ (dualRep D M) M).hom ≫ evalPairing D M) (rfl : 0 + 2 = 2) y x := by
        rw [tensorHom_toDualDual_evalPairing]
    _ = cohomologyMap (evalPairing D M) 2
          (cohomologyMap (β_ (dualRep D M) M).hom 2 (cup (rfl : 0 + 2 = 2) y x)) := by
        rw [cupPairing_apply, cohomologyMap_comp]
        rfl
    _ = cupPairing (evalPairing D M) (rfl : 2 + 0 = 2) x y := by
        rw [cohomologyMap_braiding_cup (rfl : 0 + 2 = 2) (rfl : 2 + 0 = 2) y x, zero_mul, pow_zero,
          one_smul]
        rfl

end Generic

section Two

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) Γ} [IsDiscreteRep D]
  {t : cohomology D 2 →+ ZMod n}

omit [NeZero n] in

theorem dualityMap_two_eq (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    [IsDiscreteRep (dualRep D (dualRep D M))] (x : cohomology M 2)
    (y : cohomology (dualRep D M) 0) :
    dualityMap D (rfl : 2 + 0 = 2) t M x y =
      dualityMap D (rfl : 0 + 2 = 2) t (dualRep D M) y
        ((cohomologyMap (toDualDual D M) 2).hom x) := by
  rw [dualityMap_apply, dualityMap_apply, cupPairing_toDualDual]

namespace GroupDualityHypotheses

variable (H : GroupDualityHypotheses n D t)

include H in

theorem bijective_two (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (dualityMap D (rfl : 2 + 0 = 2) t M) := by
  have := H.finite_D
  have : Finite (cohomology M 2) := H.finite_two M hM
  have hbij := bijective_toDualDual H.nonempty_addEquiv hM
  have : IsDiscreteRep (dualRep D (dualRep D M)) := isDiscreteRep_dualRep _ _
  let e : M ≅ dualRep D (dualRep D M) := Rep.isoOfBijective (toDualDual D M) hbij
  have he1 : ∀ z, (cohomologyMap e.inv 2).hom ((cohomologyMap (toDualDual D M) 2).hom z) = z :=
    fun z => by
      change (cohomologyMap e.hom 2 ≫ cohomologyMap e.inv 2).hom z = z
      rw [← cohomologyMap_comp, e.hom_inv_id, cohomologyMap_id]
      rfl
  have he2 : ∀ z, (cohomologyMap (toDualDual D M) 2).hom ((cohomologyMap e.inv 2).hom z) = z :=
    fun z => by
      change (cohomologyMap e.inv 2 ≫ cohomologyMap e.hom 2).hom z = z
      rw [← cohomologyMap_comp, e.inv_hom_id, cohomologyMap_id]
      rfl
  have h0 := H.bijective_zero (dualRep D M) (nsmul_dualRep_eq_zero H.nsmul_D)
  refine bijective_of_bijective_flip (nsmul_cohomology_eq_zero _ hM 2)
    (bilinAddHom (cupPairing (evalPairing D M) (rfl : 2 + 0 = 2))) t ?_
  let c := (cohomologyMap (toDualDual D M) 2).hom.toAddMonoidHom
  let c' := (cohomologyMap e.inv 2).hom.toAddMonoidHom
  have hpre : Function.Bijective fun χ : cohomology (dualRep D (dualRep D M)) 2 →+ ZMod n =>
      χ.comp c := by
    constructor
    · intro χ χ' h
      ext z
      have := congrArg (fun f : cohomology M 2 →+ ZMod n => f ((c' z))) h
      simpa [c, c', he2] using this
    · intro ξ
      refine ⟨ξ.comp c', ?_⟩
      ext z
      simp [c, c', he1]
  have hfun : (fun y => t.comp ((bilinAddHom (cupPairing (evalPairing D M)
      (rfl : 2 + 0 = 2))).flip y)) =
      fun y => (dualityMap D (rfl : 0 + 2 = 2) t (dualRep D M) y).comp c := by
    funext y
    ext x
    exact dualityMap_two_eq M x y
  rw [hfun]
  exact hpre.comp h0

include H in

theorem bijective_dualityMap (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective (dualityMap D h t M) := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (r = 0 ∧ s = 2) ∨ (r = 1 ∧ s = 1) ∨ (r = 2 ∧ s = 0) := by omega
  · exact H.bijective_zero M hM
  · exact H.bijective_one M hM
  · exact H.bijective_two M hM

end GroupDualityHypotheses

end Two

end GroundTheory.ProfCoh
