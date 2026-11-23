import Mathlib
import GroundTheory.ProfiniteCohomology.TorsionDualFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

namespace Involution

variable {M : Type*} [AddCommGroup M]

def fixedSub (σ : M →+ M) : AddSubgroup M := (σ - AddMonoidHom.id M).ker

theorem mem_fixedSub {σ : M →+ M} {x : M} : x ∈ fixedSub σ ↔ σ x = x := by
  rw [fixedSub, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]

def traceSub (σ : M →+ M) : AddSubgroup M := (AddMonoidHom.id M + σ).range

theorem mem_traceSub {σ : M →+ M} {x : M} : x ∈ traceSub σ ↔ ∃ y, y + σ y = x := by
  rw [traceSub, AddMonoidHom.mem_range]
  rfl

theorem traceSub_le_fixedSub {σ : M →+ M} (hσ : ∀ x, σ (σ x) = x) : traceSub σ ≤ fixedSub σ := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_traceSub.1 hx
  rw [mem_fixedSub, map_add, hσ, add_comm]

abbrev tateQuot (σ : M →+ M) : Type _ :=
  fixedSub σ ⧸ (traceSub σ).addSubgroupOf (fixedSub σ)

def dualInv (σ : M →+ M) : (M →+ QZ) →+ (M →+ QZ) where
  toFun f := -(f.comp σ)
  map_zero' := by ext; simp
  map_add' f g := by ext; simp [add_comm]

@[simp]
theorem dualInv_apply (σ : M →+ M) (f : M →+ QZ) (x : M) : dualInv σ f x = -f (σ x) :=
  rfl

theorem mem_fixedSub_dualInv_iff {σ : M →+ M} (f : M →+ QZ) :
    f ∈ fixedSub (dualInv σ) ↔ ∀ y, f (y + σ y) = 0 := by
  rw [mem_fixedSub]
  constructor
  · intro h y
    have e := DFunLike.congr_fun h y
    rw [dualInv_apply] at e
    rw [map_add, ← e, neg_add_cancel]
  · intro h
    ext y
    rw [dualInv_apply, neg_eq_iff_add_eq_zero, add_comm, ← map_add]
    exact h y

def fixedPair (σ : M →+ M) : fixedSub σ →+ fixedSub (dualInv σ) →+ QZ where
  toFun x :=
    { toFun := fun f => (f : M →+ QZ) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem fixedPair_apply (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    fixedPair σ x f = (f : M →+ QZ) x :=
  rfl

theorem two_nsmul_fixedPair (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    2 • fixedPair σ x f = 0 := by
  rw [fixedPair_apply, two_nsmul]
  have hx : σ x = x := mem_fixedSub.1 x.2
  have hf := (mem_fixedSub_dualInv_iff (f : M →+ QZ)).1 f.2 x
  rwa [hx, map_add] at hf

theorem fixedPair_eq_zero_of_mem_left (σ : M →+ M) (x : fixedSub σ) (hx : (x : M) ∈ traceSub σ)
    (f : fixedSub (dualInv σ)) : fixedPair σ x f = 0 := by
  obtain ⟨y, hy⟩ := mem_traceSub.1 hx
  rw [fixedPair_apply, ← hy]
  exact (mem_fixedSub_dualInv_iff (f : M →+ QZ)).1 f.2 y

theorem fixedPair_eq_zero_of_mem_right (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ))
    (hf : (f : M →+ QZ) ∈ traceSub (dualInv σ)) : fixedPair σ x f = 0 := by
  obtain ⟨g, hg⟩ := mem_traceSub.1 hf
  have hx : σ x = x := mem_fixedSub.1 x.2
  rw [fixedPair_apply, ← hg, AddMonoidHom.add_apply, dualInv_apply, hx, add_neg_cancel]

def tatePair (σ : M →+ M) : tateQuot σ →+ tateQuot (dualInv σ) →+ QZ :=
  QuotientAddGroup.lift _
    { toFun := fun x => QuotientAddGroup.lift _ (fixedPair σ x) fun f hf =>
        fixedPair_eq_zero_of_mem_right σ x f hf
      map_zero' := by
        ext f
        simp
      map_add' := fun x y => by
        ext f
        simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, AddMonoidHom.add_apply,
          QuotientAddGroup.lift_mk, map_add]
        rfl }
    fun x hx => by
      ext f
      exact fixedPair_eq_zero_of_mem_left σ x hx f

@[simp]
theorem tatePair_mk (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    tatePair σ (x : tateQuot σ) (f : tateQuot (dualInv σ)) = (f : M →+ QZ) x :=
  rfl

variable {σ : M →+ M}

theorem tatePair_injective : Function.Injective (tatePair σ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  by_contra hne
  have hne' : (QuotientAddGroup.mk (x : M) : M ⧸ traceSub σ) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨χ, hχ⟩ := QZ.exists_apply_ne_zero hne'
  set f : M →+ QZ := χ.comp (QuotientAddGroup.mk' (traceSub σ)) with hf_def
  have hf : f ∈ fixedSub (dualInv σ) := by
    rw [mem_fixedSub_dualInv_iff]
    intro y
    rw [hf_def, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      (QuotientAddGroup.eq_zero_iff _).2 (mem_traceSub.2 ⟨y, rfl⟩), map_zero]
  apply hχ
  exact DFunLike.congr_fun hx (((⟨f, hf⟩ : fixedSub (dualInv σ))) : tateQuot (dualInv σ))

theorem tatePair_flip_injective : Function.Injective (tatePair σ).flip := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective f
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  have hker : (AddMonoidHom.id M - σ).ker ≤ (f : M →+ QZ).ker := by
    intro x hx
    have hx' : (x : M) ∈ fixedSub σ := by
      rw [mem_fixedSub]
      rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero] at hx
      exact hx.symm
    exact DFunLike.congr_fun hf (((⟨x, hx'⟩ : fixedSub σ)) : tateQuot σ)
  obtain ⟨ψ, hψ⟩ := QZ.exists_comp_eq_of_ker_le _ _ hker
  refine mem_traceSub.2 ⟨ψ, ?_⟩
  rw [← hψ]
  ext x
  simp [sub_eq_add_neg]

instance finite_tateQuot [Finite M] (τ : M →+ M) : Finite (tateQuot τ) :=
  inferInstance

theorem tatePair_bijective [Finite M] : Function.Bijective (tatePair σ) := by
  have : Finite (tateQuot (dualInv σ) →+ QZ) := Nat.finite_of_card_ne_zero (by
    rw [QZ.card_hom]; exact Nat.card_pos.ne')
  refine (tatePair_injective (σ := σ)).bijective_of_nat_card_le ?_
  rw [QZ.card_hom]
  have h := Nat.card_le_card_of_injective _ (tatePair_flip_injective (σ := σ))
  rwa [QZ.card_hom] at h

theorem tatePair_flip_bijective [Finite M] : Function.Bijective (tatePair σ).flip := by
  have : Finite (tateQuot σ →+ QZ) := Nat.finite_of_card_ne_zero (by
    rw [QZ.card_hom]; exact Nat.card_pos.ne')
  refine (tatePair_flip_injective (σ := σ)).bijective_of_nat_card_le ?_
  rw [QZ.card_hom]
  have h := Nat.card_le_card_of_injective _ (tatePair_injective (σ := σ))
  rwa [QZ.card_hom] at h

section Transport

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

def fixedSubCongr (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x)) :
    fixedSub σ ≃+ fixedSub τ where
  toFun x := ⟨e (x : M), mem_fixedSub.2 (by rw [← he, mem_fixedSub.1 x.2])⟩
  invFun y := ⟨e.symm (y : N), mem_fixedSub.2 (by
    apply e.injective
    rw [he, e.apply_symm_apply, mem_fixedSub.1 y.2])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : M))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : N))
  map_add' x y := Subtype.ext (map_add e (x : M) (y : M))

@[simp]
theorem coe_fixedSubCongr_apply (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N}
    (he : ∀ x, e (σ x) = τ (e x)) (x : fixedSub σ) : (fixedSubCongr e he x : N) = e (x : M) :=
  rfl

def tateQuotCongr (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x)) :
    tateQuot σ ≃+ tateQuot τ :=
  QuotientAddGroup.congr _ _ (fixedSubCongr e he) (by
    ext y
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := mem_traceSub.1 hx
      refine mem_traceSub.2 ⟨e z, ?_⟩
      show e z + τ (e z) = e (x : M)
      rw [← he, ← map_add, hz]
    · intro hy
      refine ⟨(fixedSubCongr e he).symm y, ?_, AddEquiv.apply_symm_apply _ _⟩
      obtain ⟨z, hz⟩ := mem_traceSub.1 hy
      refine mem_traceSub.2 ⟨e.symm z, ?_⟩
      apply e.injective
      rw [map_add, he, e.apply_symm_apply, hz]
      change (y : N) = e (e.symm (y : N))
      rw [e.apply_symm_apply])

@[simp]
theorem tateQuotCongr_mk (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x))
    (x : fixedSub σ) :
    tateQuotCongr e he (x : tateQuot σ) = (fixedSubCongr e he x : tateQuot τ) :=
  rfl

end Transport

section Pairings

variable {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']

theorem bijective_of_pairing_eq (P : X →+ Y →+ QZ) (Q : X' →+ Y' →+ QZ) (e : X' ≃+ X) (e' : Y' ≃+ Y)
    (h : ∀ x y, P (e x) (e' y) = Q x y) (hQ : Function.Bijective Q) : Function.Bijective P := by
  let pre : (Y' →+ QZ) ≃ (Y →+ QZ) :=
    { toFun := fun φ => φ.comp e'.symm.toAddMonoidHom
      invFun := fun ψ => ψ.comp e'.toAddMonoidHom
      left_inv := fun φ => by ext; simp
      right_inv := fun ψ => by ext; simp }
  have hP : ⇑P = pre ∘ Q ∘ e.symm := by
    funext x
    ext y
    change P x y = Q (e.symm x) (e'.symm y)
    rw [← h, e.apply_symm_apply, e'.apply_symm_apply]
  rw [hP]
  exact pre.bijective.comp (hQ.comp e.symm.bijective)

theorem bijective_flip_of_pairing_eq (P : X →+ Y →+ QZ) (Q : X' →+ Y' →+ QZ) (e : X' ≃+ X)
    (e' : Y' ≃+ Y) (h : ∀ x y, P (e x) (e' y) = Q x y) (hQ : Function.Bijective Q.flip) :
    Function.Bijective P.flip :=
  bijective_of_pairing_eq P.flip Q.flip e' e (fun y x => h x y) hQ

end Pairings

end Involution

end GroundTheory.ProfCoh
