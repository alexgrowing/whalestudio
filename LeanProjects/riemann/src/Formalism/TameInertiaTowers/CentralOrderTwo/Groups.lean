import Mathlib
import Formalism.TameInertiaTowers.StatementGroup

open Subgroup
open scoped commutatorElement

namespace Formalism.TwoAdicCyclotomicDecomposition

theorem centralExtAbelian : CentralExtAbelian := by
  intro H G _ _ π _hsurj hker D hD hcase x y
  rcases hcase with hcomp | ⟨hDtop, hDab⟩
  ·
    have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
      intro a ha b hb
      have hmem : a * b * (b * a)⁻¹ ∈ D ⊓ π.ker := by
        refine ⟨D.mul_mem (D.mul_mem ha hb) (D.inv_mem (D.mul_mem hb ha)), ?_⟩
        refine MonoidHom.mem_ker.mpr ?_
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (π a) (π b), mul_inv_cancel]
      rw [hcomp, Subgroup.mem_bot] at hmem
      exact mul_inv_eq_one.mp hmem

    have hdec : ∀ x : H, ∃ d ∈ D, ∃ z ∈ Subgroup.center H, x = d * z := by
      intro x
      have hx : π x ∈ D.map π := by rw [hD]; exact Subgroup.mem_top _
      obtain ⟨d, hdD, hdx⟩ := Subgroup.mem_map.mp hx
      refine ⟨d, hdD, d⁻¹ * x, hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
    obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := hdec x
    obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := hdec y
    have c1 := Subgroup.mem_center_iff.mp hz₁
    have c2 := Subgroup.mem_center_iff.mp hz₂
    calc d₁ * z₁ * (d₂ * z₂) = d₁ * d₂ * (z₁ * z₂) := by
          rw [mul_assoc d₁ z₁, ← mul_assoc z₁ d₂, ← c1 d₂]; group
      _ = d₂ * d₁ * (z₂ * z₁) := by rw [hDcomm d₁ hd₁ d₂ hd₂, c1 z₂]
      _ = d₂ * z₂ * (d₁ * z₁) := by
          rw [mul_assoc d₂ z₂, ← mul_assoc z₂ d₁, ← c2 d₁]; group
  · exact hDab x (hDtop ▸ Subgroup.mem_top x) y (hDtop ▸ Subgroup.mem_top y)

section CommGen

variable {H : Type} [Group H]

theorem comm_mul_left_of_central (hcen : commutator H ≤ Subgroup.center H) (a b y : H) :
    ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆ := by
  have hc : ∀ z : H, z * ⁅b, y⁆ = ⁅b, y⁆ * z := fun z =>
    Subgroup.mem_center_iff.mp (hcen (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top b) (Subgroup.mem_top y))) z
  calc ⁅a * b, y⁆ = a * (⁅b, y⁆ * (y * a⁻¹ * y⁻¹)) := by
        simp only [commutatorElement_def]; group
    _ = a * ((y * a⁻¹ * y⁻¹) * ⁅b, y⁆) := by rw [hc]
    _ = ⁅a, y⁆ * ⁅b, y⁆ := by simp only [commutatorElement_def]; group

def commLeftSub (hcen : commutator H ≤ Subgroup.center H) (C : Subgroup H) (y : H) :
    Subgroup H where
  carrier := {x | ⁅x, y⁆ ∈ C}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [comm_mul_left_of_central hcen]
    exact C.mul_mem ha hb
  one_mem' := by
    simp only [Set.mem_ofPred_eq, commutatorElement_one_left]
    exact C.one_mem
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ⁅a⁻¹, y⁆ * ⁅a, y⁆ = 1 := by
      rw [← comm_mul_left_of_central hcen, inv_mul_cancel, commutatorElement_one_left]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact C.inv_mem ha

end CommGen

theorem commGen : CommGen := by
  intro H _ g hgen hcen h01
  set C := Subgroup.closure
    ({⁅g 0, g 2⁆, ⁅g 0, g 3⁆, ⁅g 1, g 2⁆, ⁅g 1, g 3⁆, ⁅g 2, g 3⁆} : Set H) with hCdef
  have h01' : ⁅g 0, g 1⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h01
  have h10' : ⁅g 1, g 0⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h01.symm
  have hbase : ∀ i j : Fin 4, ⁅g i, g j⁆ ∈ C := by
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp only <;>
      first
      | (rw [commutatorElement_self]; exact C.one_mem)
      | (simp [h01', h10']; done)
      | (apply Subgroup.subset_closure; simp; done)
      | (rw [← commutatorElement_inv]; apply C.inv_mem; apply Subgroup.subset_closure; simp; done)
  have hall : ∀ x y : H, ⁅x, y⁆ ∈ C := by
    have h1 : ∀ (i : Fin 4) (y : H), ⁅y, g i⁆ ∈ C := by
      intro i y
      have hle : Subgroup.closure (Set.range g) ≤ commLeftSub hcen C (g i) := by
        rw [Subgroup.closure_le]; rintro _ ⟨j, rfl⟩; exact hbase j i
      exact hle (hgen ▸ Subgroup.mem_top y)
    intro x y
    have hle : Subgroup.closure (Set.range g) ≤ commLeftSub hcen C y := by
      rw [Subgroup.closure_le]; rintro _ ⟨i, rfl⟩
      show ⁅g i, y⁆ ∈ C
      rw [← commutatorElement_inv]; exact C.inv_mem (h1 i y)
    exact hle (hgen ▸ Subgroup.mem_top x)
  have heq : commutator H = C := by
    apply le_antisymm
    · rw [commutator_eq_closure, Subgroup.closure_le]
      rintro _ ⟨x, y, rfl⟩; exact hall x y
    · rw [hCdef, Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;>
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  refine ⟨heq, ?_⟩
  intro hsq
  let c : Fin 5 → H := ![⁅g 0, g 2⁆, ⁅g 0, g 3⁆, ⁅g 1, g 2⁆, ⁅g 1, g 3⁆, ⁅g 2, g 3⁆]
  have hcmem : ∀ i, c i ∈ commutator H := by
    intro i; rw [heq, hCdef]; apply Subgroup.subset_closure
    fin_cases i <;> simp [c]
  have hcomm : Pairwise fun i j : Fin 5 => ∀ x y : H, x ∈ Subgroup.zpowers (c i) →
      y ∈ Subgroup.zpowers (c j) → Commute x y := by
    intro i j _ x y hx _
    have hxc : x ∈ Subgroup.center H := (Subgroup.zpowers_le.mpr (hcen (hcmem i))) hx
    exact (Subgroup.mem_center_iff.mp hxc y).symm
  let φ := Subgroup.noncommPiCoprod hcomm
  have hfin : ∀ i, Nat.card (Subgroup.zpowers (c i)) ≤ 2 := by
    intro i; rw [Nat.card_zpowers]; exact orderOf_le_of_pow_eq_one (by norm_num) (hsq _ (hcmem i))
  have : ∀ i, Finite (Subgroup.zpowers (c i)) := fun i => Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, by norm_num, hsq _ (hcmem i)⟩)).ne')
  have hle : C ≤ φ.range := by
    rw [hCdef, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hi : ∃ i, c i = z := by
      rcases hz with rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
    obtain ⟨i, rfl⟩ := hi
    exact ⟨Pi.mulSingle i ⟨c i, Subgroup.mem_zpowers _⟩, by simp [φ]⟩
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  calc Nat.card (commutator H) = Nat.card C := by rw [heq]
    _ ≤ Nat.card φ.range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (∀ i, Subgroup.zpowers (c i)) :=
        Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
    _ = ∏ i, Nat.card (Subgroup.zpowers (c i)) := Nat.card_pi
    _ ≤ ∏ _i : Fin 5, 2 := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hfin i)
    _ = 2 ^ 5 := by simp

theorem rankBound : RankBound := by
  intro r hr
  constructor
  · intro h
    by_contra hlt
    have h1 : r * 4 ≤ r * (r - 1) := Nat.mul_le_mul_left r (by omega)
    generalize r * (r - 1) = t at h h1
    omega
  · intro h
    interval_cases r <;> decide

end Formalism.TwoAdicCyclotomicDecomposition
