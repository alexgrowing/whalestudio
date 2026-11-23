import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllSet

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace TypAr

variable {C : Type} [Field C] {V : VF C}

theorem ge_lpow (k : ℕ) : V.Ge (k : ℝ) ((V.l : C) ^ k) := by
  induction k with
  | zero => simpa using VF.Ge.one (V := V)
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul VF.ge_l
    convert this using 1
    push_cast; ring

theorem ge_of_lpow_dvd {k m : ℕ} (h : V.l ^ k ∣ m) : V.Ge (k : ℝ) (m : C) := by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_mul, Nat.cast_pow]
  simpa using (ge_lpow (V := V) k).mul (VF.ge_natCast t)

theorem vlim_const {N : Type} {a : ℕ → C} {b : C} (h : ∀ K : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, V.Ge K (b - a k)) :
    VLim V (fun k (_ : ℕ) (_ : N) => a k) (fun _ _ => b) := fun K _ _ => h K

theorem eventually_ge_nat (K : ℝ) (c : ℕ) : ∃ k0 : ℕ, ∀ k ≥ k0, K ≤ ((k + c : ℕ) : ℝ) := by
  obtain ⟨k0, hk0⟩ := exists_nat_ge K
  refine ⟨k0, fun k hk => ?_⟩
  have : (k0 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast
  have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  linarith

theorem typ_gen {N : Type} (M : Set (ℕ → N → C))
    (hroot : ∀ p : ℕ, p.Prime → p ≠ V.l → ∃ ζ : C, IsPrimitiveRoot ζ p)
    (h1 : 1 ∈ M) (hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M) (hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M)
    (hteich : ∀ c : C, V.Ge 0 c → (fun n (_ : N) => c ^ n) ∈ M)
    (hlim : ∀ (m : ℕ → ℕ → N → C) (m' : ℕ → N → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M) :
    (fun n (_ : N) => if ∃ s, V.l ^ s = n then (1 : C) else 0) ∈ M := by
  have hl2 := V.l_prime.two_le

  have hconst : ∀ k : ℕ, (fun (_ : ℕ) (_ : N) => ((k + 1 : ℕ) : C)) ∈ M := by
    intro k
    induction k with
    | zero => convert h1 using 1; funext n x; simp
    | succ k ih =>
      have := hadd _ _ ih h1
      convert this using 1
      funext n x; simp only [Pi.add_apply, Pi.one_apply]; push_cast; ring

  have h0 : (0 : ℕ → N → C) ∈ M := by
    have hm : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) ∈ M := fun k => hconst _
    have e : ∀ k, ((V.l ^ k - 1 + 1 : ℕ) : C) = (V.l : C) ^ k := fun k => by
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ V.l_prime.pos)]; push_cast; rfl
    refine hlim (fun k (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) 0 hm ?_
    intro K s x
    obtain ⟨k0, hk0⟩ := eventually_ge_nat K 0
    refine ⟨k0, fun k hk => ?_⟩
    simp only [Pi.zero_apply, zero_sub, e]
    exact ((ge_lpow k).neg).mono (by simpa using hk0 k hk)

  have hneg : ∀ m, m ∈ M → -m ∈ M := by
    intro m hm
    have hc : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) * m ∈ M :=
      fun k => hmul _ _ (hconst _) hm
    have e : ∀ k, ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C) = (V.l : C) ^ (k + 1) - 1 := fun k => by
      have h2 : 2 ≤ V.l ^ (k + 1) := le_trans hl2 (Nat.le_self_pow (Nat.succ_ne_zero k) _)
      have : V.l ^ (k + 1) - 2 + 1 = V.l ^ (k + 1) - 1 := by omega
      rw [this, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    have hv : VLim V (fun k (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) (fun _ _ => (-1 : C)) := by
      apply vlim_const
      intro K
      obtain ⟨k0, hk0⟩ := eventually_ge_nat K 1
      refine ⟨k0, fun k hk => ?_⟩
      rw [e]
      have : (-1 : C) - ((V.l : C) ^ (k + 1) - 1) = -((V.l : C) ^ (k + 1)) := by ring
      rw [this]
      exact ((ge_lpow (k + 1)).neg).mono (by simpa using hk0 k hk)
    have := hlim _ _ hc (hv.mul_right m)
    convert this using 1
    funext n x; simp
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∑ i ∈ s, f i) ∈ M := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact hadd _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∏ i ∈ s, f i) ∈ M := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact hmul _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hpow : ∀ m, m ∈ M → ∀ e : ℕ, m ^ e ∈ M := by
    intro m hm e
    induction e with
    | zero => simpa using h1
    | succ e ih => rw [pow_succ]; exact hmul _ _ ih hm

  have hD : ∀ p : ℕ, p.Prime → p ≠ V.l → (fun n (_ : N) => if p ∣ n then (1 : C) else 0) ∈ M := by
    intro p hp hpl
    obtain ⟨ζ, hζ⟩ := hroot p hp hpl
    have hζi : ∀ j : ℕ, V.Ge 0 (ζ ^ j) := fun j =>
      VF.ge_of_pow_eq_one V hp.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    set G : ℕ → N → C := ∑ j ∈ Finset.range p, fun n (_ : N) => (ζ ^ j) ^ n with hG
    have hGM : G ∈ M := hsum _ _ fun j _ => hteich _ (hζi j)
    have hGv : ∀ n x, G n x = if p ∣ n then (p : C) else 0 := by
      intro n x
      rw [hG, Finset.sum_apply, Finset.sum_apply]
      have e : ∀ j ∈ Finset.range p, (ζ ^ j) ^ n = (ζ ^ n) ^ j := fun j _ => by
        rw [← pow_mul, ← pow_mul, mul_comm]
      rw [Finset.sum_congr rfl e]
      by_cases hn : p ∣ n
      · rw [if_pos hn]
        obtain ⟨t, rfl⟩ := hn
        rw [pow_mul, hζ.pow_eq_one, one_pow]
        simp
      · rw [if_neg hn]
        have hcop : n.Coprime p := (Nat.coprime_comm.trans (Nat.Prime.coprime_iff_not_dvd hp)).mpr hn
        exact (hζ.pow_of_coprime n hcop).geom_sum_eq_zero hp.one_lt
    refine hlim (fun k => G ^ Nat.totient (V.l ^ (k + 1))) _ (fun k => hpow _ hGM _) ?_
    intro K n x
    obtain ⟨k0, hk0⟩ := eventually_ge_nat K 1
    refine ⟨k0, fun k hk => ?_⟩
    have hφ : 0 < Nat.totient (V.l ^ (k + 1)) := Nat.totient_pos.mpr (pow_pos V.l_prime.pos _)
    show V.Ge K ((if p ∣ n then (1 : C) else 0) - (G ^ Nat.totient (V.l ^ (k + 1))) n x)
    rw [Pi.pow_apply, Pi.pow_apply, hGv]
    by_cases hn : p ∣ n
    · rw [if_pos hn, if_pos hn]
      have hcop : p.Coprime (V.l ^ (k + 1)) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hp V.l_prime).mpr hpl)
      have hmod := Nat.ModEq.pow_totient hcop
      have hdvd : V.l ^ (k + 1) ∣ p ^ Nat.totient (V.l ^ (k + 1)) - 1 :=
        (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp hmod.symm
      have hge := ge_of_lpow_dvd (V := V) hdvd
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow, Nat.cast_one] at hge
      have : (1 : C) - (p : C) ^ Nat.totient (V.l ^ (k + 1)) = -((p : C) ^ Nat.totient (V.l ^ (k + 1)) - 1) := by ring
      rw [this]
      exact hge.neg.mono (by simpa using hk0 k hk)
    · rw [if_neg hn, if_neg hn, zero_pow hφ.ne', sub_zero]
      exact VF.Ge.zero K

  set S : ℕ → Finset ℕ := fun P => (Finset.range (P + 1)).filter fun p => p.Prime ∧ p ≠ V.l with hS
  set T : ℕ → ℕ → N → C := fun P => ∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0)) with hT
  have hTM : ∀ P, T P ∈ M := fun P => hprod _ _ fun p hp => by
    have hp' := (Finset.mem_filter.mp hp).2
    exact hadd _ _ h1 (hneg _ (hD p hp'.1 hp'.2))
  refine hlim T _ hTM ?_
  intro K n x
  refine ⟨n + 3, fun P hP => ?_⟩
  show V.Ge K ((if ∃ s, V.l ^ s = n then (1 : C) else 0) - T P n x)
  have hTv : T P n x = ∏ p ∈ S P, (1 - if p ∣ n then (1 : C) else 0) := by
    show (∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0))) n x = _
    rw [Finset.prod_apply, Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro p _
    simp [sub_eq_add_neg]
  rw [hTv]
  by_cases hpow' : ∃ s, V.l ^ s = n
  · rw [if_pos hpow']
    obtain ⟨s, rfl⟩ := hpow'
    have : ∏ p ∈ S P, (1 - if p ∣ V.l ^ s then (1 : C) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hnd : ¬ p ∣ V.l ^ s := fun h => hp'.2 ((Nat.prime_dvd_prime_iff_eq hp'.1 V.l_prime).mp (hp'.1.dvd_of_dvd_pow h))
      rw [if_neg hnd, sub_zero]
    rw [this, sub_self]
    exact VF.Ge.zero K
  · rw [if_neg hpow']
    have hex : ∃ p ∈ S P, p ∣ n := by
      by_cases hn0 : n = 0
      · subst hn0
        by_cases hl2' : V.l = 2
        · refine ⟨3, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_three, by omega⟩, dvd_zero 3⟩
        · refine ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two, fun h => hl2' h.symm⟩, dvd_zero 2⟩
      · by_contra hne
        push_neg at hne
        apply hpow'
        refine ⟨n.primeFactorsList.length, (Nat.eq_prime_pow_of_unique_prime_dvd hn0 ?_).symm⟩
        intro q hq hqn
        by_contra hql
        have hqle : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqn
        exact hne q (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hql⟩) hqn
    obtain ⟨p, hpS, hpn⟩ := hex
    rw [Finset.prod_eq_zero hpS (by rw [if_pos hpn, sub_self]), sub_zero]
    exact VF.Ge.zero K

end TypAr

end Formalism.L2.FormalSeriesBounds
