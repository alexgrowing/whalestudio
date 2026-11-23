import Mathlib

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem fibre_sum_le {α β : Type*} (π : α → β) (f : α → ℝ) (h : β → ℝ) (n : ℕ) (hf0 : ∀ a, 0 ≤ f a)
    (hfh : ∀ a, f a ≤ h (π a)) (hh0 : ∀ b, 0 ≤ h b) (hh : Summable h)
    (hfib : ∀ b, {a | π a = b}.Finite ∧ {a | π a = b}.ncard ≤ n) :
    Summable f ∧ ∑' a, f a ≤ n * ∑' b, h b := by
  classical
  have key : ∀ u : Finset α, ∑ a ∈ u, f a ≤ n * ∑' b, h b := by
    intro u
    calc ∑ a ∈ u, f a ≤ ∑ a ∈ u, h (π a) := Finset.sum_le_sum fun a _ => hfh a
      _ = ∑ b ∈ u.image π, ∑ a ∈ u.filter (fun a => π a = b), h (π a) :=
          (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem π ha) _).symm
      _ ≤ ∑ b ∈ u.image π, (n : ℝ) * h b := by
          refine Finset.sum_le_sum fun b _ => ?_
          have e : ∑ a ∈ u.filter (fun a => π a = b), h (π a)
              = ∑ a ∈ u.filter (fun a => π a = b), h b :=
            Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]
          rw [e, Finset.sum_const, nsmul_eq_mul]
          have hc : (u.filter (fun a => π a = b)).card ≤ n := by
            have := Set.ncard_le_ncard (s := ((u.filter (fun a => π a = b) : Finset α) : Set α))
              (t := {a | π a = b}) (fun a ha => (Finset.mem_filter.1 ha).2) (hfib b).1
            rw [Set.ncard_coe_finset] at this
            exact this.trans (hfib b).2
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hh0 b)
      _ = n * ∑ b ∈ u.image π, h b := (Finset.mul_sum _ _ _).symm
      _ ≤ n * ∑' b, h b :=
          mul_le_mul_of_nonneg_left (hh.sum_le_tsum _ fun b _ => hh0 b) (Nat.cast_nonneg n)
  have hs : Summable f := summable_of_sum_le (fun a => hf0 a) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩

theorem fibre_sum_ge {α β : Type*} (π : α → β) (f : α → ℝ) (g : β → ℝ) (k : ℕ) (hf0 : ∀ a, 0 ≤ f a)
    (hf : Summable f) (hg0 : ∀ b, 0 ≤ g b) (hg : Summable g) (S : Set β) (hS : S.Finite)
    (hfib : ∀ b ∉ S, k ≤ {a | π a = b ∧ f a = g b}.ncard) :
    (k : ℝ) * ∑' b, g b ≤ ∑' a, f a + k * ∑' b, S.indicator g b := by
  classical
  have hf0' : 0 ≤ ∑' a, f a := tsum_nonneg hf0
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hf0'
  have hfin : ∀ b ∉ S, {a | π a = b ∧ f a = g b}.Finite := fun b hb =>
    Set.finite_of_ncard_pos (lt_of_lt_of_le hk (hfib b hb))
  let A : β → Finset α := fun b => if hb : b ∉ S then (hfin b hb).toFinset else ∅
  have hA : ∀ b a, a ∈ A b → π a = b ∧ f a = g b := by
    intro b a ha
    simp only [A] at ha
    split_ifs at ha with hb
    all_goals simp at ha
    all_goals exact ha
  have hcard : ∀ b ∉ S, k ≤ (A b).card := by
    intro b hb
    simp only [A, dif_pos hb]
    rw [← Set.ncard_eq_toFinset_card _ (hfin b hb)]
    exact hfib b hb
  have hdisj : ∀ v : Finset β, (v : Set β).PairwiseDisjoint A := by
    intro v b _ b' _ hbb'
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    exact hbb' ((hA b a ha).1.symm.trans (hA b' a ha').1)
  have hmain : ∀ v : Finset β, ∑ b ∈ v, (k : ℝ) * Sᶜ.indicator g b ≤ ∑' a, f a := by
    intro v
    calc ∑ b ∈ v, (k : ℝ) * Sᶜ.indicator g b ≤ ∑ b ∈ v, ∑ a ∈ A b, f a := by
          refine Finset.sum_le_sum fun b _ => ?_
          by_cases hb : b ∈ S
          · rw [Set.indicator_of_notMem (by simpa using hb), mul_zero]
            exact Finset.sum_nonneg fun a _ => hf0 a
          · rw [Set.indicator_of_mem (by simpa using hb)]
            have e : ∑ a ∈ A b, f a = ∑ a ∈ A b, g b :=
              Finset.sum_congr rfl fun a ha => (hA b a ha).2
            rw [e, Finset.sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard b hb) (hg0 b)
      _ = ∑ a ∈ v.biUnion A, f a := (Finset.sum_biUnion (hdisj v)).symm
      _ ≤ ∑' a, f a := hf.sum_le_tsum _ fun a _ => hf0 a
  have h1 : ∑' b, (k : ℝ) * Sᶜ.indicator g b ≤ ∑' a, f a := tsum_le_of_sum_le' hf0' hmain
  rw [Summable.tsum_mul_left _ (hg.indicator _)] at h1
  have h2 : ∑' b, g b = ∑' b, Sᶜ.indicator g b + ∑' b, S.indicator g b := by
    rw [← Summable.tsum_add (hg.indicator _) (hg.indicator _)]
    congr 1
    ext b
    rw [add_comm, Set.indicator_self_add_compl_apply]
  rw [h2, mul_add]
  linarith

end ReciprocityTheory.Cheb
