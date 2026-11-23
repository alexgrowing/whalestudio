import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_oneUnits_iff_exists_eq_one_add {O : Type} [CommRing O] (t : O) (u : Oˣ) :
    u ∈ oneUnits t ↔ ∃ x : O, (u : O) = 1 + t * x := by
  unfold oneUnits
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change Ideal.Quotient.mk (Ideal.span {t}) (u : O) = Ideal.Quotient.mk (Ideal.span {t}) 1 ↔ _
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← hx]; ring⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [hx]; ring⟩

theorem relIndex_oneUnits_mul_eq_card_quotient :
    ∀ (O : Type) [CommRing O] [IsDomain O] (t s : O), t ≠ 0 → s ∣ t →
      Ideal.span {t} ≤ Ideal.jacobson (⊥ : Ideal O) →
      (oneUnits (s * t)).relIndex (oneUnits t) = Nat.card (O ⧸ Ideal.span {s}) := by
  intro O _ _ t s ht hst hJ
  have hex : ∀ u : oneUnits t, ∃ x : O, ((u : Oˣ) : O) = 1 + t * x := fun u =>
    (mem_oneUnits_iff_exists_eq_one_add t u).1 u.2
  choose c hc using hex
  have huniq : ∀ (u : oneUnits t) (x : O), ((u : Oˣ) : O) = 1 + t * x → c u = x := by
    intro u x hx
    have h := hc u
    rw [hx] at h
    exact (mul_left_cancel₀ ht (add_left_cancel h)).symm
  let f : oneUnits t →* Multiplicative (O ⧸ Ideal.span {s}) :=
    { toFun := fun u => Multiplicative.ofAdd (Ideal.Quotient.mk (Ideal.span {s}) (c u))
      map_one' := by
        rw [huniq 1 0 (by simp)]
        simp
      map_mul' := by
        intro u v
        rw [huniq (u * v) (c u + c v + t * (c u * c v)) (by
          rw [Subgroup.coe_mul, Units.val_mul, hc u, hc v]; ring), ← ofAdd_add, ← map_add]
        congr 1
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        have : c u + c v + t * (c u * c v) - (c u + c v) = t * (c u * c v) := by ring
        rw [this]
        exact hst.mul_right _ }
  have hf : ∀ u, f u = Multiplicative.ofAdd (Ideal.Quotient.mk (Ideal.span {s}) (c u)) :=
    fun _ => rfl
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (Multiplicative.toAdd y)
    have hu : IsUnit (t * x + 1) :=
      Ideal.mem_jacobson_bot.1 (hJ (Ideal.mem_span_singleton_self t)) x
    have hval : ((hu.unit : Oˣ) : O) = 1 + t * x := by rw [hu.unit_spec, add_comm]
    refine ⟨⟨hu.unit, (mem_oneUnits_iff_exists_eq_one_add t _).2 ⟨x, hval⟩⟩, ?_⟩
    rw [hf, huniq _ x hval, hx]
    rfl
  have hker : (oneUnits (s * t)).subgroupOf (oneUnits t) = f.ker := by
    ext u
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hf, mem_oneUnits_iff_exists_eq_one_add,
      ofAdd_eq_one, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, huniq u _ (by rw [hx]; ring)⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [hc u, hx]; ring⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj,
    Subgroup.card_top]
  rfl

end GlobalTheory.CNorm
