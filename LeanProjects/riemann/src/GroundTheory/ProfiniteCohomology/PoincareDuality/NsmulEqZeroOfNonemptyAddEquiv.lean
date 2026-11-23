import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
import GroundTheory.ProfiniteCohomology.CartierDual
import GroundTheory.ProfiniteCohomology.ClassFormations.CorestrictionDefs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section Dual

variable {k G : Type u} [CommRing k] [Group G]

abbrev dualRep (D M : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (Representation.linHom M.ρ D.ρ)

theorem dualRep_eq_ihom (D M : Rep.{u} k G) : dualRep D M = (Rep.ihom M).obj D :=
  rfl

theorem dualRep_ρ_apply (D M : Rep.{u} k G) (σ : G) (f : M →ₗ[k] D) (m : M) :
    ((dualRep D M).ρ σ f : M →ₗ[k] D) m = D.ρ σ (f (M.ρ σ⁻¹ m)) :=
  rfl

def dualMap (D : Rep.{u} k G) {A B : Rep.{u} k G} (φ : A ⟶ B) : dualRep D B ⟶ dualRep D A :=
  Rep.ofHom ⟨{ toFun := fun f => f ∘ₗ φ.hom.toLinearMap
               map_add' := fun f g => rfl
               map_smul' := fun r f => rfl }, fun σ => by
    refine LinearMap.ext fun f => LinearMap.ext fun a => ?_
    change D.ρ σ (f (B.ρ σ⁻¹ (φ.hom a))) = D.ρ σ (f (φ.hom (A.ρ σ⁻¹ a)))
    rw [Rep.hom_comm_apply]⟩

@[simp]
theorem dualMap_hom_apply (D : Rep.{u} k G) {A B : Rep.{u} k G} (φ : A ⟶ B) (f : B →ₗ[k] D)
    (a : A) : ((dualMap D φ).hom f : A →ₗ[k] D) a = f (φ.hom a) :=
  rfl

theorem dualMap_id (D A : Rep.{u} k G) : dualMap D (𝟙 A) = 𝟙 (dualRep D A) :=
  rfl

theorem dualMap_comp (D : Rep.{u} k G) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    dualMap D (φ ≫ ψ) = dualMap D ψ ≫ dualMap D φ :=
  rfl

def dualEvalBilin (D M : Rep.{u} k G) : M →ₗ[k] (M →ₗ[k] D) →ₗ[k] D where
  toFun m :=
    { toFun := fun f => f m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' a b := LinearMap.ext fun f => f.map_add a b
  map_smul' r a := LinearMap.ext fun f => f.map_smul r a

def evalPairing (D M : Rep.{u} k G) : M ⊗ dualRep D M ⟶ D :=
  pairingHom (dualEvalBilin D M) fun σ m f => by
    change D.ρ σ (f (M.ρ σ⁻¹ (M.ρ σ m))) = D.ρ σ (f m)
    rw [Representation.inv_self_apply]

@[simp]
theorem evalPairing_tmul (D M : Rep.{u} k G) (m : M) (f : M →ₗ[k] D) :
    (evalPairing D M).hom (m ⊗ₜ[k] (f : dualRep D M) : (M ⊗ dualRep D M : Rep k G)) = f m :=
  pairingHom_tmul (A := M) (B := dualRep D M) (dualEvalBilin D M) _ m f

theorem tensorHom_evalPairing (D : Rep.{u} k G) {A B : Rep.{u} k G} (φ : A ⟶ B) :
    (φ ⊗ₘ 𝟙 (dualRep D B)) ≫ evalPairing D B = (𝟙 A ⊗ₘ dualMap D φ) ≫ evalPairing D A := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def toDualDual (D M : Rep.{u} k G) : M ⟶ dualRep D (dualRep D M) :=
  Rep.ofHom ⟨dualEvalBilin D M, fun σ => by
    refine LinearMap.ext fun m => LinearMap.ext fun f => ?_
    change f (M.ρ σ m) = D.ρ σ (D.ρ σ⁻¹ (f (M.ρ σ⁻¹⁻¹ m)))
    rw [inv_inv, Representation.self_inv_apply]⟩

@[simp]
theorem toDualDual_hom_apply (D M : Rep.{u} k G) (m : M) (f : M →ₗ[k] D) :
    ((toDualDual D M).hom m : (M →ₗ[k] D) →ₗ[k] D) f = f m :=
  rfl

end Dual

section Discrete

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance isDiscreteRep_dualRep (D M : Rep.{u} k G) [IsDiscreteRep D] [IsDiscreteRep M]
    [Finite M] : IsDiscreteRep (dualRep D M) := by
  refine ⟨fun f => Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_⟩
  have hmem : (⋂ m : M, ((stabilizer M.ρ m : Set G) ∩ (stabilizer D.ρ (f m) : Set G))) ∈
      nhds (1 : G) :=
    Filter.iInter_mem.2 fun m => Filter.inter_mem
      ((isOpen_stabilizer M m).mem_nhds (one_mem _))
      ((isOpen_stabilizer D (f m)).mem_nhds (one_mem _))
  refine Filter.mem_of_superset hmem fun σ hσ => ?_
  simp only [Set.mem_iInter, Set.mem_inter_iff, SetLike.mem_coe, mem_stabilizer] at hσ
  change (dualRep D M).ρ σ f = f
  refine LinearMap.ext fun m => ?_
  have hm : M.ρ σ⁻¹ m = m := (stabilizer M.ρ m).inv_mem (hσ m).1
  rw [dualRep_ρ_apply, hm, (hσ m).2]

end Discrete

section Pairing

variable {k : Type u} [CommRing k]

def bilinAddHom {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module k X]
    [Module k Y] [Module k Z] (β : X →ₗ[k] Y →ₗ[k] Z) : X →+ Y →+ Z where
  toFun x := (β x).toAddMonoidHom
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem bilinAddHom_apply {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module k X] [Module k Y] [Module k Z] (β : X →ₗ[k] Y →ₗ[k] Z) (x : X) (y : Y) :
    bilinAddHom β x y = β x y :=
  rfl

def IsPerfectPairing {n : ℕ} {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (β : X →+ Y →+ Z) (t : Z →+ ZMod n) : Prop :=
  Function.Bijective (fun x : X => t.comp (β x)) ∧
    Function.Bijective (fun y : Y => t.comp (β.flip y))

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def dualityMap (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ} (h : r + s = m)
    (t : cohomology D m →+ ZMod n) (M : Rep.{u} k G) [IsDiscreteRep M]
    [IsDiscreteRep (dualRep D M)] :
    cohomology M r →+ (cohomology (dualRep D M) s →+ ZMod n) where
  toFun x := t.comp (bilinAddHom (cupPairing (evalPairing D M) h) x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem dualityMap_apply (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ} (h : r + s = m)
    (t : cohomology D m →+ ZMod n) (M : Rep.{u} k G) [IsDiscreteRep M]
    [IsDiscreteRep (dualRep D M)] (x : cohomology M r) (y : cohomology (dualRep D M) s) :
    dualityMap D h t M x y = t (cupPairing (evalPairing D M) h x y) :=
  rfl

end Pairing

section ZModMul

variable {G : Type u} [Group G]

theorem nsmul_eq_zero_of_nonempty_addEquiv {n : ℕ} {D : Type*} [AddCommGroup D]
    (h : Nonempty (D ≃+ ZMod n)) (d : D) : n • d = 0 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_nsmul, map_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem zsmul_eq_zsmul_of_intCast_eq {n : ℕ} {D : Type*} [AddCommGroup D]
    (hD : ∀ d : D, n • d = 0) {a b : ℤ} (h : (a : ZMod n) = b) (d : D) : a • d = b • d := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a n).1 h.symm
  have h0 : (a - b) • d = 0 := by
    rw [hc, mul_comm, mul_zsmul, natCast_zsmul, hD, zsmul_zero]
  rwa [sub_smul, sub_eq_zero] at h0

def zmodMulAddHom (n : ℕ) {D : Type*} [AddCommGroup D] (hD : ∀ d : D, n • d = 0) :
    ZMod n →+ D →+ D where
  toFun a :=
    { toFun := fun d => (ZMod.cast a : ℤ) • d
      map_zero' := zsmul_zero _
      map_add' := fun d d' => zsmul_add _ _ _ }
  map_zero' := by
    ext d
    simp
  map_add' a b := by
    ext d
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply, ← add_zsmul]
    exact zsmul_eq_zsmul_of_intCast_eq hD (by push_cast; simp) d

theorem zmodMulAddHom_apply (n : ℕ) {D : Type*} [AddCommGroup D] (hD : ∀ d : D, n • d = 0)
    (a : ZMod n) (d : D) : zmodMulAddHom n hD a d = (ZMod.cast a : ℤ) • d :=
  rfl

def bilinOfAddHom {k : Type*} [CommRing k] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module k A] [Module k B] [Module k C] (f : A →+ B →+ C)
    (h₁ : ∀ (c : k) (a : A) (b : B), f (c • a) b = c • f a b)
    (h₂ : ∀ (c : k) (a : A) (b : B), f a (c • b) = c • f a b) : A →ₗ[k] B →ₗ[k] C :=
  LinearMap.mk₂ k (fun a b => f a b) (fun a a' b => by simp) h₁ (fun a b b' => by simp) h₂

def zmodMulPairing (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) G) (hD : ∀ d : D, n • d = 0) :
    zmodRep.{u} G n ⊗ D ⟶ D :=
  pairingHom
    (bilinOfAddHom ((zmodMulAddHom n hD).comp
      ((AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).toAddMonoidHom.comp
        (AddMonoidHom.id (zmodRep.{u} G n))))
      (fun c a d => by
        obtain ⟨c⟩ := c
        have h : (ULift.up c : ULift.{u} ℤ) = ((c : ℤ) : ULift.{u} ℤ) := by
          ext
          simp
        rw [h, Int.cast_smul_eq_zsmul (ULift.{u} ℤ), Int.cast_smul_eq_zsmul (ULift.{u} ℤ),
          map_zsmul, AddMonoidHom.zsmul_apply])
      (fun c a d => by
        obtain ⟨c⟩ := c
        have h : (ULift.up c : ULift.{u} ℤ) = ((c : ℤ) : ULift.{u} ℤ) := by
          ext
          simp
        rw [h, Int.cast_smul_eq_zsmul (ULift.{u} ℤ), Int.cast_smul_eq_zsmul (ULift.{u} ℤ),
          map_zsmul]))
    fun σ a d => by
      change zmodMulAddHom n hD (ULift.down (a : ULift.{u} (ZMod n))) (D.ρ σ d) =
        D.ρ σ (zmodMulAddHom n hD (ULift.down (a : ULift.{u} (ZMod n))) d)
      rw [zmodMulAddHom_apply, zmodMulAddHom_apply, map_zsmul]

@[simp]
theorem zmodMulPairing_tmul (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) G) (hD : ∀ d : D, n • d = 0)
    (a : ZMod n) (d : D) :
    (zmodMulPairing n D hD).hom ((ULift.up a : zmodRep.{u} G n) ⊗ₜ[ULift.{u} ℤ] d :
      (zmodRep.{u} G n ⊗ D : Rep _ _)) = (ZMod.cast a : ℤ) • d :=
  by
    rw [zmodMulPairing, pairingHom_tmul]
    rfl

end ZModMul

section Hypotheses

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

structure DualityHypotheses (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D] where

  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)

  finite_cohomology : ∀ (U : OpenSubgroup G) (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G))
    [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) → ∀ r ≤ 2, Finite (cohomology M r)

  subsingleton_cohomology_three : ∀ (U : OpenSubgroup G)
    (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G)) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (cohomology M 3)

  t : ∀ U : OpenSubgroup G, cohomology (Rep.res (U : Subgroup G).subtype D) 2 ≃+ ZMod n

  t_cores : ∀ (U V : OpenSubgroup G) (h : V ≤ U)
    (x : cohomology (Rep.res (V : Subgroup G).subtype D) 2),
    t U (cohomologyCoresLE D h 2 x) = t V x

  isPerfectPairing : ∀ U : OpenSubgroup G,
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n (Rep.res (U : Subgroup G).subtype D)
        (nsmul_eq_zero_of_nonempty_addEquiv nonempty_addEquiv)) (show 1 + 1 = 2 from rfl)))
      (t U).toAddMonoidHom

end Hypotheses

end GroundTheory.ProfCoh
