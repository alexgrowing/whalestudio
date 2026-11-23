import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

noncomputable section

namespace GlobalTheory.Shin.HcUnit

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

variable {F : Type} [Field F]

theorem toG_val {n : ℕ} (x : GL (Fin n) F) : toG (x : Matrix (Fin n) (Fin n) F) = x := by
  unfold toG
  rw [dif_pos x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem brG_zero {a : ℕ} (x : GL (Fin a) F) : brG 0 a x = x := by
  have h : br 0 a (x : Matrix (Fin a) (Fin a) F) = x := by
    ext i j
    simp [br, ent]
  unfold brG
  rw [h, toG_val]

theorem tlG_self {a : ℕ} (x : GL (Fin a) F) : tlG a x = x := by
  have h : tl a (x : Matrix (Fin a) (Fin a) F) = x := by
    ext i j
    simp [tl, ent]
  unfold tlG
  rw [h, toG_val]

theorem inPar_zero {n : ℕ} (x : GL (Fin n) F) : InPar 0 x :=
  fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem inPar_self {a : ℕ} (x : GL (Fin a) F) : InPar a x :=
  fun i _ _ hi => absurd i.isLt (not_lt.mpr hi)

theorem gal_id {n : ℕ} (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

theorem mean_class {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsCl χ) (x : G) :
    (Nat.card G : ℂ)⁻¹ * ∑ᶠ y : G, χ (y⁻¹ * x * y) = χ x := by
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h' : ∀ y : G, χ (y⁻¹ * x * y) = χ x := fun y => h x y
  have := Fintype.ofFinite G
  rw [finsum_congr h', finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

private theorem card_infinitePlace_eq_f {G : Type} {p : G → Prop} (h : ∀ x, p x) :
    Nat.card {x // p x} = Nat.card G :=
  Nat.card_congr (Equiv.subtypeUnivEquiv h)

theorem main : ∀ (F : Type) [Field F] [Finite F], ∀ (a : ℕ) (α : GL (Fin a) F → ℂ), IsCl α →
    hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α := by
  intro F _ _ a α hα
  refine ⟨funext fun x => ?_, funext fun x => ?_⟩
  · simp only [hc, hcTw]
    rw [card_infinitePlace_eq_f inPar_zero]
    simp only [gal_id, inPar_zero, ↓reduceIte, brG_zero, one_mul]
    exact mean_class hα x
  · simp only [hc, hcTw]
    rw [card_infinitePlace_eq_f inPar_self]
    simp only [gal_id, inPar_self, ↓reduceIte, tlG_self, mul_one]
    exact mean_class hα x

end GlobalTheory.Shin.HcUnit

end
