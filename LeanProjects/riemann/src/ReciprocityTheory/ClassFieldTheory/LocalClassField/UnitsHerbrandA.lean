import Mathlib

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

section approx

variable {U : Type*} [CommGroup U]

theorem exists_of_approx (V : ℕ → Subgroup U)
    (hcomp : ∀ v : ℕ → U, (∀ k, v k ∈ V k) → ∃ s ∈ V 0, ∀ n, s / ∏ k ∈ range n, v k ∈ V n)
    (hsep : ∀ u, (∀ n, u ∈ V n) → u = 1) (Z : Subgroup U) (f : U →* U)
    (hfV : ∀ n, ∀ u ∈ V n, f u ∈ V n) (hfZ : ∀ u, f u ∈ Z)
    (step : ∀ n, ∀ u ∈ V n, u ∈ Z → ∃ v ∈ V n, u / f v ∈ V (n + 1)) :
    ∀ u ∈ V 0, u ∈ Z → ∃ v ∈ V 0, f v = u := by
  classical
  intro u hu hZ
  choose! c hc using step
  let w : ℕ → U := fun n => Nat.rec u (fun n x => x / f (c n x)) n
  have hw : ∀ n, w n ∈ V n ∧ w n ∈ Z := by
    intro n
    induction n with
    | zero => exact ⟨hu, hZ⟩
    | succ n ih => exact ⟨(hc n _ ih.1 ih.2).2, Z.div_mem ih.2 (hfZ _)⟩
  have hprod : ∀ n, w n = u / f (∏ k ∈ range n, c k (w k)) := by
    intro n
    induction n with
    | zero => simp [w]
    | succ n ih =>
      rw [prod_range_succ, map_mul, ← div_div, ← ih]
  obtain ⟨s, hs0, hs⟩ := hcomp (fun k => c k (w k)) (fun k => (hc k _ (hw k).1 (hw k).2).1)
  refine ⟨s, hs0, ?_⟩
  have h1 : u / f s = 1 := hsep _ fun n => by
    have h2 : u / f s = w n / f (s / ∏ k ∈ range n, c k (w k)) := by
      rw [hprod n, map_div, div_div_div_cancel_right]
    rw [h2]
    exact (V n).div_mem (hw n).1 (hfV n _ (hs n))
  exact (div_eq_one.1 h1).symm

end approx

variable {R : Type*} [Field R] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G R]

structure Filt (I : ℕ → AddSubgroup R) (e : R →+ R) : Prop where
  anti : ∀ n, I (n + 1) ≤ I n
  mul : ∀ n x y, x ∈ I n → y ∈ I 0 → x * y ∈ I (n + 1)
  smul : ∀ n (g : G) x, x ∈ I n → g • x ∈ I n
  comp : ∀ x : ℕ → R, (∀ k, x k ∈ I k) → ∃ s, ∀ n, s - ∑ k ∈ range n, x k ∈ I n
  sep : ∀ x, (∀ n, x ∈ I n) → x = 0
  inv : ∀ n x, x ∈ I n → (1 + x)⁻¹ - 1 ∈ I n
  e_mem : ∀ n x, x ∈ I n → e x ∈ I n
  e_sum : ∀ x, ∑ g : G, g • e (g⁻¹ • x) = x

namespace Filt

variable {G} {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)

include h

theorem le_zero (n : ℕ) : I n ≤ I 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (h.anti n).trans ih

theorem mul_unit {n : ℕ} {x u : R} (hx : x ∈ I n) (hu : u - 1 ∈ I 0) : x * u ∈ I n := by
  have : x * u = x * (u - 1) + x := by ring
  rw [this]
  exact (I n).add_mem (h.anti n (h.mul n _ _ hx hu)) hx

theorem one_add_ne_zero {x : R} (hx : x ∈ I 0) : 1 + x ≠ 0 := by
  intro h0
  have h1 : (1 : R) ∈ I 0 := by
    have : (1 : R) = - x := by linear_combination h0
    rw [this]; exact (I 0).neg_mem hx
  have hn : ∀ n, (1 : R) ∈ I n := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih => simpa using h.mul n 1 1 ih h1
  exact one_ne_zero (h.sep 1 hn)

def V (n : ℕ) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I n}
  one_mem' := by simp
  mul_mem' := fun {u v} hu hv => by
    have hu' : (u : R) - 1 ∈ I n := hu
    have hv' : (v : R) - 1 ∈ I n := hv
    show ((u * v : Rˣ) : R) - 1 ∈ I n
    have : ((u * v : Rˣ) : R) - 1 = ((u : R) - 1) * v + ((v : R) - 1) := by
      rw [Units.val_mul]; ring
    rw [this]
    exact (I n).add_mem (h.mul_unit hu' (h.le_zero n hv')) hv'
  inv_mem' := fun {u} hu => by
    have hu' : (u : R) - 1 ∈ I n := hu
    show ((u⁻¹ : Rˣ) : R) - 1 ∈ I n
    have := h.inv n _ hu'
    rwa [add_sub_cancel, ← Units.val_inv_eq_inv_val] at this

theorem mem_V {n : ℕ} {u : Rˣ} : u ∈ h.V n ↔ (u : R) - 1 ∈ I n := Iff.rfl

theorem V_le_zero (n : ℕ) : h.V n ≤ h.V 0 := fun _ hu => h.le_zero n hu

noncomputable def mkU (x : R) (hx : x ∈ I 0) : Rˣ := Units.mk0 (1 + x) (h.one_add_ne_zero hx)

theorem mkU_val (x : R) (hx : x ∈ I 0) : (h.mkU x hx : R) = 1 + x := rfl

theorem mkU_mem {n : ℕ} (x : R) (hx : x ∈ I n) : h.mkU x (h.le_zero n hx) ∈ h.V n := by
  rw [mem_V, mkU_val, add_sub_cancel_left]; exact hx

theorem div_mem_V {n : ℕ} {u v : Rˣ} (hv : v ∈ h.V 0) (huv : (u : R) - v ∈ I n) : u / v ∈ h.V n := by
  rw [mem_V]
  have : ((u / v : Rˣ) : R) - 1 = ((u : R) - v) * ((v⁻¹ : Rˣ) : R) := by
    rw [div_eq_mul_inv, Units.val_mul, sub_mul, Units.mul_inv]
  rw [this]
  exact h.mul_unit huv ((h.V 0).inv_mem hv)

theorem prod_one_add {ι : Type*} {n : ℕ} (s : Finset ι) (y : ι → R) (hy : ∀ j ∈ s, y j ∈ I n) :
    ∏ j ∈ s, (1 + y j) - 1 - ∑ j ∈ s, y j ∈ I (n + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hE := ih fun j hj => hy j (mem_insert_of_mem hj)
    have hS : ∑ j ∈ s, y j ∈ I n := (I n).sum_mem fun j hj => hy j (mem_insert_of_mem hj)
    have hya := hy a (mem_insert_self a s)
    rw [prod_insert ha, sum_insert ha]
    have : (1 + y a) * ∏ j ∈ s, (1 + y j) - 1 - (y a + ∑ j ∈ s, y j) =
        (∏ j ∈ s, (1 + y j) - 1 - ∑ j ∈ s, y j) + y a * (∏ j ∈ s, (1 + y j) - 1 - ∑ j ∈ s, y j)
          + y a * ∑ j ∈ s, y j := by ring
    rw [this]
    exact (I (n + 1)).add_mem ((I (n + 1)).add_mem hE (h.mul n _ _ hya (h.le_zero _ hE)))
      (h.mul n _ _ hya (h.le_zero _ hS))

theorem V_comp (v : ℕ → Rˣ) (hv : ∀ k, v k ∈ h.V k) :
    ∃ s ∈ h.V 0, ∀ n, s / ∏ k ∈ range n, v k ∈ h.V n := by
  have hP : ∀ n, ∏ k ∈ range n, v k ∈ h.V 0 := fun n =>
    (h.V 0).prod_mem fun k _ => h.V_le_zero k (hv k)
  have hx : ∀ k, ((v k : R) - 1) * ((∏ j ∈ range k, v j : Rˣ) : R) ∈ I k := fun k =>
    h.mul_unit (hv k) (hP k)
  obtain ⟨t, ht⟩ := h.comp _ hx
  have hsum : ∀ n, ∑ k ∈ range n, ((v k : R) - 1) * ((∏ j ∈ range k, v j : Rˣ) : R) =
      ((∏ j ∈ range n, v j : Rˣ) : R) - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, prod_range_succ, Units.val_mul]; ring
  have ht0 : t ∈ I 0 := by simpa using ht 0
  refine ⟨h.mkU t ht0, h.mkU_mem t ht0, fun n => h.div_mem_V (hP n) ?_⟩
  have := ht n
  rw [hsum] at this
  rw [mkU_val]
  convert this using 1
  ring

theorem V_sep (u : Rˣ) (hu : ∀ n, u ∈ h.V n) : u = 1 :=
  Units.ext (sub_eq_zero.1 (h.sep _ hu))

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
