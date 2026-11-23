import Mathlib
import Formalism.PeriodIntegrals.ArtSch

namespace PI.ArtSch.WittLiftWork

open WittVector

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k]

noncomputable abbrev I (n : ℕ) : Ideal (WittVector p k) := RingHom.ker (WittVector.truncate (p := p) (R := k) n)

theorem mem_I {n : ℕ} {x : WittVector p k} : x ∈ I n ↔ ∀ i < n, x.coeff i = 0 := by
  first
    | exact WittVector.mem_ker_truncate x
    | exact WittVector.mem_ker_truncate
    | rw [RingHom.mem_ker]
      constructor
      · intro h i hi
        have h' := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
        simpa [WittVector.coeff_truncate] using h'
      · intro h
        refine TruncatedWittVector.ext fun i => ?_
        simpa [WittVector.coeff_truncate] using h i i.2

theorem I_anti {m n : ℕ} (h : n ≤ m) {x : WittVector p k} (hx : x ∈ I m) : x ∈ I n :=
  mem_I.2 fun i hi => mem_I.1 hx i (Nat.lt_of_lt_of_le hi h)

theorem I_zero (x : WittVector p k) : x ∈ I 0 :=
  mem_I.2 fun i hi => absurd hi (Nat.not_lt_zero i)

theorem coeff_eq_of_sub_mem {n : ℕ} {a b : WittVector p k} (hab : a - b ∈ I n) {i : ℕ} (hi : i < n) :
    a.coeff i = b.coeff i := by
  have h0 := RingHom.mem_ker.1 hab
  rw [map_sub, sub_eq_zero] at h0
  have h1 := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h0
  simpa [WittVector.coeff_truncate] using h1

theorem sub_mem_of_coeff_eq {n : ℕ} {a b : WittVector p k} (h : ∀ i < n, a.coeff i = b.coeff i) :
    a - b ∈ I n := by
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  refine TruncatedWittVector.ext fun i => ?_
  simpa [WittVector.coeff_truncate] using h i i.2

theorem sub_coeff_zero' (a c : WittVector p k) : (a - c).coeff 0 = a.coeff 0 - c.coeff 0 := by
  have h := WittVector.add_coeff_zero (a - c) c
  rw [sub_add_cancel] at h
  rw [h]
  ring

theorem iter_sub (n : ℕ) (a b : WittVector p k) :
    verschiebung^[n] (a - b) = verschiebung^[n] a - verschiebung^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_sub]

theorem map_iter (f : k →+* k) (n : ℕ) (a : WittVector p k) :
    WittVector.map f (verschiebung^[n] a) = verschiebung^[n] (WittVector.map f a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact WittVector.map_verschiebung f _

theorem iter_coeff_lt (n : ℕ) (a : WittVector p k) : ∀ i < n, (verschiebung^[n] a).coeff i = 0 := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ j => exact (WittVector.verschiebung_coeff_succ _ j).trans (ih j (by omega))

private theorem coeff_iterate_verschiebung_add (n : ℕ) (a : WittVector p k) (i : ℕ) :
    (verschiebung^[n] a).coeff (i + n) = a.coeff i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (WittVector.verschiebung_coeff_succ (verschiebung^[n] a) (i + n)).trans (ih i)

theorem iter_coeff_self (n : ℕ) (a : WittVector p k) : (verschiebung^[n] a).coeff n = a.coeff 0 := by
  have h := coeff_iterate_verschiebung_add n a 0
  rwa [Nat.zero_add] at h

theorem iterate_verschiebung_mem_I (n : ℕ) (a : WittVector p k) : verschiebung^[n] a ∈ I n :=
  mem_I.2 (iter_coeff_lt n a)

section
variable [CharP k p]

noncomputable def δ (x : WittVector p k) : WittVector p k := WittVector.map (frobenius k p) x - x

theorem δ_add (a b : WittVector p k) : δ (a + b) = δ a + δ b := by
  show WittVector.map (frobenius k p) (a + b) - (a + b) =
    (WittVector.map (frobenius k p) a - a) + (WittVector.map (frobenius k p) b - b)
  rw [map_add]
  abel

theorem δ_mem {n : ℕ} {z : WittVector p k} (hz : z ∈ I n) : δ z ∈ I n := by
  show WittVector.map (frobenius k p) z - z ∈ I n
  have h1 : WittVector.map (frobenius k p) z ∈ I n := by
    refine mem_I.2 fun i hi => ?_
    rw [WittVector.map_coeff, mem_I.1 hz i hi, map_zero]
  exact Ideal.sub_mem _ h1 hz

theorem δ_iter (n : ℕ) (a : WittVector p k) : δ (verschiebung^[n] a) = verschiebung^[n] (δ a) := by
  show WittVector.map (frobenius k p) (verschiebung^[n] a) - verschiebung^[n] a =
    verschiebung^[n] (WittVector.map (frobenius k p) a - a)
  rw [map_iter, iter_sub]

private theorem eq_iterate_verschiebung_mk_shift {n : ℕ} {z : WittVector p k} (hz : z ∈ I n) :
    z = verschiebung^[n] (WittVector.mk p fun i => z.coeff (i + n)) := by
  refine WittVector.ext fun i => ?_
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [mem_I.1 hz i hi, iter_coeff_lt n _ i hi]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + n := ⟨i - n, by omega⟩
    exact (coeff_iterate_verschiebung_add n (WittVector.mk p fun i => z.coeff (i + n)) j).symm

private theorem coeff_sub_of_mem_I {n : ℕ} {x y : WittVector p k} (hx : x ∈ I n) (hy : y ∈ I n) :
    (x - y).coeff n = x.coeff n - y.coeff n := by
  obtain ⟨x', hx'⟩ : ∃ x', x = verschiebung^[n] x' := ⟨_, eq_iterate_verschiebung_mk_shift hx⟩
  obtain ⟨y', hy'⟩ : ∃ y', y = verschiebung^[n] y' := ⟨_, eq_iterate_verschiebung_mk_shift hy⟩
  subst hx' hy'
  rw [← iter_sub]
  simp only [iter_coeff_self]
  exact sub_coeff_zero' x' y'

theorem δ_teich_coeff_zero (b : k) : (δ (teichmuller p b)).coeff 0 = b ^ p - b := by
  show (WittVector.map (frobenius k p) (teichmuller p b) - teichmuller p b).coeff 0 = b ^ p - b
  rw [sub_coeff_zero', WittVector.map_coeff]
  rw [WittVector.teichmuller_coeff_zero, frobenius_def]

variable (hAS : ∀ a : k, ∃ y : k, y ^ p - y = a)
include hAS

theorem step {n : ℕ} (r : WittVector p k) (hr : r ∈ I n) :
    ∃ b : k, r - δ (verschiebung^[n] (teichmuller p b)) ∈ I (n + 1) := by
  obtain ⟨b, hb⟩ := hAS (r.coeff n)
  refine ⟨b, ?_⟩
  have hs : δ (verschiebung^[n] (teichmuller p b)) ∈ I n := by
    rw [δ_iter]
    exact iterate_verschiebung_mem_I n _
  have hsn : (δ (verschiebung^[n] (teichmuller p b))).coeff n = r.coeff n := by
    rw [δ_iter, iter_coeff_self,
      δ_teich_coeff_zero, hb]
  refine mem_I.2 fun i hi => ?_
  rcases Nat.lt_or_ge i n with h | h
  · exact mem_I.1 (Ideal.sub_mem _ hr hs) i h
  · obtain rfl : i = n := by omega
    rw [coeff_sub_of_mem_I hr hs, hsn, sub_self]

noncomputable def seq (x : WittVector p k) : (n : ℕ) → {y : WittVector p k // x - δ y ∈ I n}
  | 0 => ⟨0, I_zero _⟩
  | n + 1 => ⟨(seq x n).1 + verschiebung^[n]
      (teichmuller p (Classical.choose (step hAS (x - δ (seq x n).1) (seq x n).2))), by
        rw [δ_add, ← sub_sub]
        exact Classical.choose_spec (step hAS (x - δ (seq x n).1) (seq x n).2)⟩

theorem seq_succ_sub (x : WittVector p k) (n : ℕ) :
    (seq hAS x (n + 1)).1 - (seq hAS x n).1 ∈ I n := by
  obtain ⟨t, ht⟩ : ∃ t, (seq hAS x (n + 1)).1 = (seq hAS x n).1 + verschiebung^[n] t := by
    exact ⟨_, rfl⟩
  rw [ht, show ∀ u v : WittVector p k, u + v - u = v from fun u v => by abel]
  exact iterate_verschiebung_mem_I n t

theorem seq_stable (x : WittVector p k) (n : ℕ) :
    ∀ m, n ≤ m → (seq hAS x m).1 - (seq hAS x n).1 ∈ I n := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction d with
  | zero =>
    simp only [Nat.add_zero, sub_self]
    exact Ideal.zero_mem _
  | succ d ih =>
    have h1 := I_anti (Nat.le_add_right n d)
      (seq_succ_sub hAS x (n + d))
    have e : (seq hAS x (n + d + 1)).1 - (seq hAS x n).1 =
        ((seq hAS x (n + d + 1)).1 - (seq hAS x (n + d)).1) +
          ((seq hAS x (n + d)).1 - (seq hAS x n).1) := by abel
    rw [show n + (d + 1) = n + d + 1 from (Nat.add_assoc n d 1).symm, e]
    exact Ideal.add_mem _ h1 ih

noncomputable def lim (x : WittVector p k) : WittVector p k :=
  WittVector.mk p (fun i => (seq hAS x (i + 1)).1.coeff i)

theorem lim_sub (x : WittVector p k) (n : ℕ) : lim hAS x - (seq hAS x n).1 ∈ I n := by
  refine sub_mem_of_coeff_eq fun i hi => ?_
  have h := seq_stable hAS x (i + 1) n (by omega)
  exact (coeff_eq_of_sub_mem h (Nat.lt_succ_self i)).symm

theorem lim_spec (x : WittVector p k) : δ (lim hAS x) = x := by
  have key : ∀ n, x - δ (lim hAS x) ∈ I n := by
    intro n
    have h1 := (seq hAS x n).2
    have h2 := δ_mem (lim_sub hAS x n)
    have h3 := δ_add (seq hAS x n).1 (lim hAS x - (seq hAS x n).1)
    rw [show (seq hAS x n).1 + (lim hAS x - (seq hAS x n).1) = lim hAS x from by abel] at h3
    have e : x - δ (lim hAS x) =
        (x - δ (seq hAS x n).1) - δ (lim hAS x - (seq hAS x n).1) := by
      rw [h3]; abel
    rw [e]
    exact Ideal.sub_mem _ h1 h2
  refine WittVector.ext fun i => ?_
  exact (coeff_eq_of_sub_mem (key (i + 1)) (Nat.lt_succ_self i)).symm

end

theorem wittLift : PI.ArtSch.WittLift := by
  intro p _ k _ _ hAS x
  exact ⟨lim hAS x, lim_spec hAS x⟩

end PI.ArtSch.WittLiftWork
