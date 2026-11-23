import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def placeAlg (E : Place (algebraMap ℂ K)) : Subalgebra ℂ K :=
  { E.ring.toSubring with algebraMap_mem' := E.const_mem }

theorem mem_placeAlg {E : Place (algebraMap ℂ K)} {e : K} : e ∈ placeAlg E ↔ e ∈ E.ring :=
  Iff.rfl

variable (κ') in

def tensMap (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' →ₐ[ℂ] K ⊗[ℂ] κ' :=
  Algebra.TensorProduct.map A.val (AlgHom.id ℂ κ')

theorem tensMap_injective (A : Subalgebra ℂ K) : Function.Injective (tensMap κ' A) := by
  have e : ⇑(tensMap κ' A) = ⇑(LinearMap.rTensor κ' A.val.toLinearMap) := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add u v hu hv => simp only [map_add, hu, hv]
  rw [e]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

def tens (A : Subalgebra ℂ K) : Subalgebra ℂ (K ⊗[ℂ] κ') := (tensMap κ' A).range

def tensEquiv (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' ≃ₐ[ℂ] tens (κ' := κ') A :=
  AlgEquiv.ofInjective _ (tensMap_injective A)

@[simp] theorem coe_tensEquiv (A : Subalgebra ℂ K) (w : A ⊗[ℂ] κ') :
    (tensEquiv A w : K ⊗[ℂ] κ') = tensMap κ' A w := rfl

theorem tmul_mem {A : Subalgebra ℂ K} {e : K} (he : e ∈ A) (b : κ') :
    e ⊗ₜ[ℂ] b ∈ tens (κ' := κ') A :=
  ⟨⟨e, he⟩ ⊗ₜ b, rfl⟩

variable {κ : Type} [Field κ] [Algebra ℂ κ]

def graphIdeal (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') :
    Ideal (tens (κ' := κ') (placeAlg E)) :=
  Ideal.span ({b | ∃ e : K, 0 < E.ord e ∧ (b : K ⊗[ℂ] κ') = e ⊗ₜ 1} ∪
    {b | ∃ a : R, (b : K ⊗[ℂ] κ') = (a : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π a)})

def gens (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ')
    (hR : E.Contains R) (t : E.ring) {k : ℕ} (z : Fin k → R) :
    Fin (k + 1) → tens (κ' := κ') (placeAlg E) :=
  Fin.cons ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩ fun i =>
    ⟨(z i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (z i)),
      sub_mem (tmul_mem (hR _ (z i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩

variable {L : Type} [Field L] [Algebra (K ⊗[ℂ] κ') L]

theorem one_notMem {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [h𝔭 : 𝔭.IsPrime] :
    (1 : tens (κ' := κ') A) ∉ 𝔭 :=
  (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top

def locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] : Subring L where
  carrier := {x | ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧
    x * algebraMap (K ⊗[ℂ] κ') L s = algebraMap (K ⊗[ℂ] κ') L a}
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * a', s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, map_mul]
    rw [← hx, ← hy]
    ring
  one_mem' := ⟨1, 1, one_notMem 𝔭, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * s' + a' * s, s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, map_mul, map_add]
    rw [← hx, ← hy]
    ring
  zero_mem' := ⟨0, 1, one_notMem 𝔭, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    refine ⟨-a, s, hs, ?_⟩
    simp only [Subalgebra.coe_neg, map_neg]
    rw [← hx]
    ring

def toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] :
    tens (κ' := κ') A →+* locAt (L := L) 𝔭 where
  toFun b := ⟨algebraMap (K ⊗[ℂ] κ') L b, b, 1, one_notMem 𝔭, by simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (b : tens (κ' := κ') A) : (toQ (L := L) 𝔭 b : L) = algebraMap (K ⊗[ℂ] κ') L b := rfl

theorem exists_mul_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (x : locAt (L := L) 𝔭) : ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧ x * toQ 𝔭 s = toQ 𝔭 a := by
  obtain ⟨x, a, s, hs, hx⟩ := x
  exact ⟨a, s, hs, Subtype.ext hx⟩

section Inj

variable {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
  (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L))
include hinj

theorem algebraMap_ne_zero {b : tens (κ' := κ') A} (hb : b ≠ 0) :
    algebraMap (K ⊗[ℂ] κ') L b ≠ 0 := fun h =>
  hb (Subtype.ext (hinj (h.trans (map_zero _).symm)))

theorem isUnit_toQ {b : tens (κ' := κ') A} (hb : b ∉ 𝔭) : IsUnit (toQ (L := L) 𝔭 b) := by
  have hb0 : algebraMap (K ⊗[ℂ] κ') L b ≠ 0 :=
    algebraMap_ne_zero hinj fun h => hb (h ▸ 𝔭.zero_mem)
  refine IsUnit.of_mul_eq_one (b := ⟨(algebraMap (K ⊗[ℂ] κ') L b)⁻¹, 1, b, hb, by simp [hb0]⟩)
    (Subtype.ext ?_)
  simp [hb0]

theorem isLocalRing_locAt : IsLocalRing (locAt (L := L) 𝔭) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
  by_cases ha : a ∈ 𝔭
  · right
    have hsa : s - a ∉ 𝔭 := fun h => hs (by simpa using add_mem h ha)
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [sub_mul, one_mul, hx, ← map_sub]
    exact isUnit_toQ 𝔭 hinj hsa
  · left
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [hx]
    exact isUnit_toQ 𝔭 hinj ha

theorem isUnit_toQ_iff {b : tens (κ' := κ') A} : IsUnit (toQ (L := L) 𝔭 b) ↔ b ∉ 𝔭 := by
  refine ⟨fun h hb => ?_, isUnit_toQ 𝔭 hinj⟩
  obtain ⟨y, hy⟩ := h.exists_right_inv
  obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 y
  have e2 : toQ (L := L) 𝔭 (b * a) = toQ 𝔭 s := by
    rw [map_mul, ← e, ← mul_assoc, hy, one_mul]
  have e3 : b * a = s := Subtype.ext (hinj (congrArg Subtype.val e2))
  exact hs (e3 ▸ 𝔭.mul_mem_right a hb)

theorem toQ_mem_maximalIdeal_iff [IsLocalRing (locAt (L := L) 𝔭)] {b : tens (κ' := κ') A} :
    toQ (L := L) 𝔭 b ∈ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ↔ b ∈ 𝔭 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_toQ_iff 𝔭 hinj, not_not]

theorem map_le_maximalIdeal [IsLocalRing (locAt (L := L) 𝔭)] :
    𝔭.map (toQ (L := L) 𝔭) ≤ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) :=
  Ideal.map_le_iff_le_comap.2 fun _ hb => (toQ_mem_maximalIdeal_iff 𝔭 hinj).2 hb

end Inj

end GlobalTheory.GraphLocal
