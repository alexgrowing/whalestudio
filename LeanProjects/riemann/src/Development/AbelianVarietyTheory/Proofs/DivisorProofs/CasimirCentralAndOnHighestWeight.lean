import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.CasimirHighest

theorem casimir_comm_gen {R I : Type*} [Ring R] [Fintype I] [DecidableEq I] (e : I → I → R)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j =
      (if j = k then e i l else 0) - (if l = i then e k j else 0)) (k l : I) :
    (∑ a, ∑ b, e a b * e b a) * e k l = e k l * ∑ a, ∑ b, e a b * e b a := by
  rw [← sub_eq_zero]
  have h : ∀ a b, e a b * e b a * e k l - e k l * (e a b * e b a) =
      ((if a = k then e a b * e b l else 0) - (if l = b then e a b * e k a else 0)) +
      ((if b = k then e a l * e b a else 0) - (if l = a then e k b * e b a else 0)) := by
    intro a b
    have : e a b * e b a * e k l - e k l * (e a b * e b a) =
        e a b * (e b a * e k l - e k l * e b a) + (e a b * e k l - e k l * e a b) * e b a := by
      noncomm_ring
    rw [this, he, he]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a = k then e a b * e b l else 0),
    Finset.sum_comm (f := fun a b => if l = a then e k b * e b a else 0)]
  simp

theorem casimir_on_highest_rat {V : Type*} [AddCommGroup V] [Module ℂ V] {m : ℕ}
    (e : Fin m → Fin m → Module.End ℂ V)
    (he : ∀ i j, e i j * e j i - e j i * e i j = e i i - e j j)
    (v : V) (κ : Fin m → ℚ) (hv : ∀ i j, i < j → e i j v = 0)
    (hκ : ∀ i, e i i v = (κ i : ℂ) • v) :
    ∑ i, ∑ j, e i j (e j i v) =
      ((∑ i, κ i ^ 2 + ∑ i : Fin m, κ i * ((m : ℚ) - 1 - 2 * (i : ℕ)) : ℚ) : ℂ) • v := by
  have key : ∀ i j, e i j (e j i v) =
      (((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0) -
        (if i < j then κ j else 0) : ℚ) : ℂ) • v := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 := congrArg (fun f : Module.End ℂ V => f v) (he i j)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hv i j h, map_zero, sub_zero,
        hκ] at h1
      rw [h1]
      simp [h, h.ne, sub_smul]
    · subst h
      simp [hκ, mul_smul]
    · simp [hv j i h, h.ne', not_lt.mpr h.le]
  have hz : ∑ i : Fin m, ∑ j : Fin m,
      ((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0) -
        (if i < j then κ j else 0) : ℚ)
      = ∑ i, κ i ^ 2 + ∑ i : Fin m, κ i * ((m : ℚ) - 1 - 2 * (i : ℕ)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if i < j then κ j else 0), ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have a1 : ∑ j : Fin m, (if i < j then κ i else 0) = ((m : ℚ) - 1 - (i : ℕ)) * κ i := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi,
        nsmul_eq_mul]
      have := i.2
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      simp
    have a2 : ∑ j : Fin m, (if j < i then κ i else 0) = ((i : ℕ) : ℚ) * κ i := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio,
        nsmul_eq_mul]
    rw [a1, a2]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp only [key]
  rw [← hz]
  simp only [Rat.cast_sum, Finset.sum_smul]

theorem act_Eab_comm {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (i j k l : Ix p q) :
    act (Eab i j) * act (Eab k l) - act (Eab k l) * act (Eab i j) =
      (if j = k then act (Eab i l) else 0) - (if l = i then act (Eab k j) else 0) := by
  have m : ∀ i j k l : Ix p q, Eab i j * Eab k l = if j = k then Eab i l else 0 := by
    intro i j k l
    split_ifs with hh
    · subst hh; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne, hh]
  rw [← h, m, m, map_sub]
  split_ifs <;> simp

theorem casimir_central_and_highest : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → (∀ Z, casimir act * act Z = act Z * casimir act) ∧ ∀ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ → (∑ a, ∑ b, if sameBlock a b then act (Eab a b) (act (Eab b a) v) else 0) = ((∑ a, μ a ^ 2 + (∑ i : Fin p, μ (.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ))) + (∑ j : Fin q, μ (.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • v := by
  intro p q V _ _ act h
  refine ⟨fun Z => ?_, fun μ v hv => ?_⟩
  · have hZ : Z = ∑ k, ∑ l, Z k l • Eab k l := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp [Eab, Matrix.smul_single]
    have hc : ∀ k l, casimir act * act (Eab k l) = act (Eab k l) * casimir act := fun k l =>
      casimir_comm_gen (fun a b => act (Eab a b)) (act_Eab_comm h) k l
    rw [hZ]
    simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, hc]
  · simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
    obtain ⟨hw, hr⟩ := hv
    have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
      (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) v
      (fun i => μ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
    have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
      (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) v
      (fun i => μ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
    have s1 : ∀ i j, sameBlock (p := p) (q := q) (.inl i) (.inl j) := fun _ _ => trivial
    have s2 : ∀ i j, sameBlock (p := p) (q := q) (.inr i) (.inr j) := fun _ _ => trivial
    have s3 : ∀ i j, ¬ sameBlock (p := p) (q := q) (.inl i) (.inr j) := fun _ _ => id
    have s4 : ∀ i j, ¬ sameBlock (p := p) (q := q) (.inr i) (.inl j) := fun _ _ => id
    simp only [Fintype.sum_sum_type, if_pos (s1 _ _), if_pos (s2 _ _), if_neg (s3 _ _),
      if_neg (s4 _ _), Finset.sum_const_zero, add_zero, zero_add]
    rw [h1, h2, ← add_smul, ← Rat.cast_add]
    congr 2
    ring

end GlobalTheory.CasimirHighest
