import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.RootNear

theorem mul_prod_congr {B ι : Type} [CommRing B] (u : B) (x y : ι → B) (S : Finset ι)
    (h : ∀ j ∈ S, u * x j = u * y j) : u * ∏ j ∈ S, x j = u * ∏ j ∈ S, y j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : u * x a = u * y a := h a (Finset.mem_insert_self a s)
    have h2 : u * ∏ j ∈ s, x j = u * ∏ j ∈ s, y j :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    calc u * (x a * ∏ j ∈ s, x j) = (u * x a) * ∏ j ∈ s, x j := by ring
      _ = (u * y a) * ∏ j ∈ s, x j := by rw [h1]
      _ = y a * (u * ∏ j ∈ s, x j) := by ring
      _ = y a * (u * ∏ j ∈ s, y j) := by rw [h2]
      _ = u * (y a * ∏ j ∈ s, y j) := by ring

theorem exists_shift {B ι : Type} [CommRing B] (I : Ideal B) (c f : ι → B) (S : Finset ι)
    (hf : ∀ j ∈ S, IsIdempotentElem (f j)) (hc : ∀ j ∈ S, f j * c j ∈ I) :
    ∃ s ∈ I, (∏ j ∈ S, (1 - f j)) ∣ ∏ j ∈ S, (c j - s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, I.zero_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, htI, hdvd⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have hfa : f a * f a = f a := hf a (Finset.mem_insert_self a s)
    have hca : f a * c a ∈ I := hc a (Finset.mem_insert_self a s)
    refine ⟨(1 - f a) * t + f a * c a, I.add_mem (I.mul_mem_left _ htI) hca, ?_⟩
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcong : (1 - f a) * ∏ j ∈ s, (c j - ((1 - f a) * t + f a * c a)) =
        (1 - f a) * ∏ j ∈ s, (c j - t) :=
      mul_prod_congr (1 - f a) _ _ s (fun j _ => by linear_combination (c a - t) * hfa)
    have hfirst : c a - ((1 - f a) * t + f a * c a) = (1 - f a) * (c a - t) := by ring
    rw [hfirst, mul_comm (1 - f a) (c a - t), mul_assoc, hcong]
    exact Dvd.dvd.mul_left (mul_dvd_mul_left (1 - f a) hdvd) _

theorem root_near (B : Type) [CommRing B] (π : B) (hπ : π ∈ nonZeroDivisors B) (hV : VAL π)
    (d M : ℕ) (b : Fin d → B) (a : B) (hd : 0 < d)
    (hprod : ∏ j, (a - b j) ∈ Ideal.span {π ^ (d * M)}) :
    ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ ∏ j, (a₁ - b j) = 0 := by
  classical
  have key : ∀ j : Fin d, ∃ e : B, IsIdempotentElem e ∧ e * (a - b j) ∈ Ideal.span {π ^ M} ∧
      (1 - e) * π ^ M ∈ Ideal.span {a - b j} := fun j =>
    hV (a - b j) (π ^ M) ⟨M, Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  choose e he1 he2 he3 using key
  have hee : ∀ j, e j * e j = e j := fun j => he1 j
  have hr : ∀ j, ∃ r : B, (1 - e j) * π ^ M = (a - b j) * r := fun j =>
    Ideal.mem_span_singleton.mp (he3 j)
  choose r hr using hr
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hprod
  obtain ⟨j0, -⟩ : ∃ j : Fin d, True := ⟨⟨0, hd⟩, trivial⟩
  obtain ⟨E, hEdef⟩ : ∃ E : B, E = ∏ j, (1 - e j) := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hEdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => by linear_combination hee j)
  have hEj : ∀ j, E * (1 - e j) = E := by
    intro j
    have hsplit : (1 - e j) * ∏ i ∈ Finset.univ.erase j, (1 - e i) = E := by
      rw [hEdef]; exact Finset.mul_prod_erase _ (fun i => 1 - e i) (Finset.mem_univ j)
    rw [← hsplit]
    linear_combination (∏ i ∈ Finset.univ.erase j, (1 - e i)) * hee j
  have hT : ∀ j, (a - b j) * (E * r j) = E * π ^ M := by
    intro j
    calc (a - b j) * (E * r j) = E * ((a - b j) * r j) := by ring
      _ = E * ((1 - e j) * π ^ M) := by rw [← hr j]
      _ = (E * (1 - e j)) * π ^ M := by ring
      _ = E * π ^ M := by rw [hEj j]
  have hEpow : ∀ n : ℕ, E ^ (n + 1) = E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hEE]
  have hEd : E ^ d = E := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', hEpow]
  have hmain : π ^ (d * M) * (q * ∏ j, (E * r j)) = π ^ (d * M) * E := by
    calc π ^ (d * M) * (q * ∏ j, (E * r j)) = (∏ j, (a - b j)) * ∏ j, (E * r j) := by
          rw [hq]; ring
      _ = ∏ j, ((a - b j) * (E * r j)) := Finset.prod_mul_distrib.symm
      _ = ∏ _j : Fin d, (E * π ^ M) := Finset.prod_congr rfl (fun j _ => hT j)
      _ = π ^ (d * M) * E := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, hEd, ← pow_mul,
            mul_comm M d]
          ring
  have hpow : π ^ (d * M) ∈ nonZeroDivisors B := pow_mem hπ _
  have hET : E = q * ∏ j, (E * r j) := by
    have h0 : (q * ∏ j, (E * r j) - E) * π ^ (d * M) = 0 := by linear_combination hmain
    exact (sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hpow).2 _ h0)).symm
  have hEa : E * (a - b j0) ∈ Ideal.span {π ^ M} := by
    rw [Ideal.mem_span_singleton]
    have hsplit : (E * r j0) * ∏ i ∈ Finset.univ.erase j0, (E * r i) = ∏ i, (E * r i) :=
      Finset.mul_prod_erase _ (fun i => E * r i) (Finset.mem_univ j0)
    refine ⟨q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E, ?_⟩
    calc E * (a - b j0) = q * (∏ i, (E * r i)) * (a - b j0) := by rw [← hET]
      _ = q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * ((a - b j0) * (E * r j0)) := by
          rw [← hsplit]; ring
      _ = π ^ M * (q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E) := by rw [hT j0]; ring
  obtain ⟨s, hs, w, hw⟩ := exists_shift (Ideal.span {π ^ M}) (fun j => a - b j) e Finset.univ
    (fun j _ => he1 j) (fun j _ => he2 j)
  have hw' : ∏ j, (a - b j - s) = E * w := by rw [hEdef]; exact hw
  obtain ⟨a₁, ha₁⟩ : ∃ x : B, x = (1 - E) * (a - s) + E * b j0 := ⟨_, rfl⟩
  refine ⟨a₁, ?_, ?_⟩
  · have h1 : a₁ - a = (E - 1) * s - E * (a - b j0) := by rw [ha₁]; ring
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hs) hEa
  · have hsplit2 : (a₁ - b j0) * ∏ i ∈ Finset.univ.erase j0, (a₁ - b i) = ∏ i, (a₁ - b i) :=
      Finset.mul_prod_erase _ (fun i => a₁ - b i) (Finset.mem_univ j0)
    have hE0 : E * ∏ i, (a₁ - b i) = 0 := by
      rw [← hsplit2]
      linear_combination E * (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * ha₁ +
        (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * (b j0 - (a - s)) * hEE
    have hcong : (1 - E) * ∏ i, (a₁ - b i) = (1 - E) * ∏ i, (a - b i - s) :=
      mul_prod_congr (1 - E) _ _ Finset.univ
        (fun j _ => by linear_combination (1 - E) * ha₁ + (a - s - b j0) * hEE)
    calc ∏ i, (a₁ - b i) = E * ∏ i, (a₁ - b i) + (1 - E) * ∏ i, (a₁ - b i) := by ring
      _ = 0 + (1 - E) * ∏ i, (a - b i - s) := by rw [hE0, hcong]
      _ = 0 := by rw [hw']; linear_combination (-w) * hEE

end GlobalTheory.CompanionTheory.RootNear
