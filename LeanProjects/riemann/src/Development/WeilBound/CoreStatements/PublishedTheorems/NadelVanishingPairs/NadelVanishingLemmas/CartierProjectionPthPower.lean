import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqIteratePrimeCharP
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KernelDifferentialPthPower

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.ProjFn

def derEnd {K : Type} [Field K] (D : Derivation ℤ K K) : AddMonoid.End K :=
  D.toLinearMap.toAddMonoidHom

theorem list_prod_apply_fixed {M : Type} [AddCommMonoid M] (l : List (AddMonoid.End M)) (y : M)
    (h : ∀ f ∈ l, f y = y) : l.prod y = y := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons]
    show f (l.prod y) = y
    rw [ih (fun g hg => h g (List.mem_cons_of_mem _ hg)), h f List.mem_cons_self]

theorem mul_list_prod_eq_zero {R : Type} [Ring R] (a b : R) (l : List R) (hb : b ∈ l)
    (hc : ∀ f ∈ l, Commute a f) (hab : a * b = 0) : a * l.prod = 0 := by
  induction l with
  | nil => simp at hb
  | cons f l ih =>
    rw [List.prod_cons, ← mul_assoc]
    rcases List.mem_cons.1 hb with rfl | hb'
    · rw [hab, zero_mul]
    · rw [(hc f List.mem_cons_self).eq, mul_assoc,
        ih hb' (fun g hg => hc g (List.mem_cons_of_mem _ hg)), mul_zero]

private theorem derivation_iterate_mul_antidiagonal {K : Type} [Field K] (D : Derivation ℤ K K) (n : ℕ) (a b : K) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        n.choose ij.1 • ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n]
    rw [Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [map_nsmul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, Function.iterate_succ_apply',
      Function.iterate_succ_apply',
      n.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.1 hij).symm,
      nsmul_add, mul_comm ((⇑D)^[ij.2] b)]

private theorem derivation_iterate_char_mul {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (D : Derivation ℤ K K) (a b : K) :
    (⇑D)^[p] (a * b) = a * (⇑D)^[p] b + b * (⇑D)^[p] a := by
  rw [derivation_iterate_mul_antidiagonal, Finset.sum_eq_add_of_mem (0, p) (p, 0)]
  · simp only [Nat.choose_zero_right, Nat.choose_self, one_smul, Function.iterate_zero, id]
    rw [mul_comm ((⇑D)^[p] a)]
  · simp
  · simp
  · intro h
    have := congrArg Prod.fst h
    exact hp.out.ne_zero this.symm
  · intro c hc hne
    obtain ⟨h1, h2⟩ := hne
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.1 hc
    have hc1 : c.1 ≠ 0 := by
      intro h0
      apply h1
      ext
      · exact h0
      · simp at hsum ⊢; omega
    have hc2 : c.1 < p := by
      rcases Nat.lt_or_ge c.1 p with h | h
      · exact h
      · exfalso
        apply h2
        ext
        · simp; omega
        · simp; omega
    have hdvd := hp.out.dvd_choose_self hc1 hc2
    rw [nsmul_eq_mul, (CharP.cast_eq_zero_iff K p _).2 hdvd, zero_mul]

private theorem derivation_eq_zero_of_kills_coords {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ)
    (D : Fin n → Derivation ℤ K K) (hd : ∀ c : K, dK c = ∑ j, D j c • dlog (x j))
    (E : Derivation ℤ K K) (hE : ∀ k, E (x k : K) = 0) (c : K) : E c = 0 := by
  rw [← E.liftKaehlerDifferential_comp_D c]
  have hc : KaehlerDifferential.D ℤ K c = ∑ j, D j c • dlog (x j) := hd c
  rw [hc, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul]
  show D j c • E.liftKaehlerDifferential
    (((↑(x j)⁻¹ : Kˣ) : K) • KaehlerDifferential.D ℤ K (x j : K)) = 0
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, hE, smul_zero, smul_zero]

private theorem derivation_iterate_char_eq_self_of_coords {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] {n : ℕ}
    (x : Fin n → Kˣ) (D : Fin n → Derivation ℤ K K)
    (hd : ∀ c : K, dK c = ∑ j, D j c • dlog (x j))
    (hD : ∀ i j, D i (x j : K) = if i = j then (x j : K) else 0) (i : Fin n) (c : K) :
    (⇑(D i))^[p] c = D i c := by
  let L : K →ₗ[ℤ] K := ((D i : K →ₗ[ℤ] K) ^ p) - (D i : K →ₗ[ℤ] K)
  have hL : ∀ a, L a = (⇑(D i))^[p] a - D i a := by
    intro a
    show ((D i : K →ₗ[ℤ] K) ^ p) a - (D i : K →ₗ[ℤ] K) a = _
    rw [Module.End.pow_apply]
    rfl
  let E : Derivation ℤ K K := Derivation.mk' L (by
    intro a b
    rw [hL, hL, hL, derivation_iterate_char_mul p, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring)
  have hE : ∀ k, E (x k : K) = 0 := by
    intro k
    show L (x k : K) = 0
    rw [hL]
    obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
    rw [hm, Function.iterate_succ_apply]
    by_cases hik : i = k
    · have hfix : D i (x k : K) = x k := by rw [hD, if_pos hik]
      rw [hfix, Function.iterate_fixed hfix, sub_self]
    · have hz : D i (x k : K) = 0 := by rw [hD, if_neg hik]
      rw [hz, Function.iterate_fixed (map_zero (D i)), sub_self]
  have := derivation_eq_zero_of_kills_coords x D hd E hE c
  have h2 : L c = 0 := this
  rw [hL, sub_eq_zero] at h2
  exact h2

private theorem derivation_comm_of_dK_eq_sum_dlog {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ)
    (D : Fin n → Derivation ℤ K K) (hd : ∀ c : K, dK c = ∑ j, D j c • dlog (x j))
    (hD : ∀ i j, D i (x j : K) = if i = j then (x j : K) else 0) (i j : Fin n) (c : K) :
    D i (D j c) = D j (D i c) := by
  have h := derivation_eq_zero_of_kills_coords x D hd ⁅D i, D j⁆ (by
    intro k
    rw [Derivation.commutator_apply]
    by_cases hik : i = k <;> by_cases hjk : j = k <;> simp [hD, hik, hjk]) c
  rw [Derivation.commutator_apply, sub_eq_zero] at h
  exact h

theorem projector_pthPow : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ) (D : Fin n → Derivation ℤ K K), IsCoord x → (∀ c : K, dK c = ∑ j, D j c • dlog (x j)) → (∀ i j, D i (x j : K) = if i = j then (x j : K) else 0) → ∀ π : AddMonoid.End K, π = (List.ofFn fun i => 1 - (show AddMonoid.End K from (D i).toLinearMap.toAddMonoidHom) ^ (p - 1)).prod → (∀ c, ∃ g : K, π c = g ^ p) ∧ ∀ g : K, π (g ^ p) = g ^ p := by
  intro K _ p _ _ n x D _hx hd hD π hπ
  have hpr : p.Prime := Fact.out
  let Dend : Fin n → AddMonoid.End K := fun i => (D i).toLinearMap.toAddMonoidHom
  have hpow : ∀ i (m : ℕ) c, (Dend i ^ m) c = (⇑(D i))^[m] c := by
    intro i m c
    rw [AddMonoid.End.coe_pow]
    rfl
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = m + 1 := ⟨p - 2, by have := hpr.two_le; omega⟩
  have hπ' : π = (List.ofFn fun i => 1 - Dend i ^ (p - 1)).prod := hπ
  have hcomm : ∀ i j, Commute (Dend i) (Dend j) := by
    intro i j
    refine AddMonoidHom.ext fun c => ?_
    exact derivation_comm_of_dK_eq_sum_dlog x D hd hD i j c
  refine ⟨?_, ?_⟩
  · intro c
    apply dK_eq_zero_imp_pow K p
    rw [hd]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hz : Dend j * π = 0 := by
      rw [hπ']
      apply mul_list_prod_eq_zero (Dend j) (1 - Dend j ^ (p - 1))
      · rw [List.mem_ofFn]
        exact ⟨j, rfl⟩
      · intro f hf
        rw [List.mem_ofFn] at hf
        obtain ⟨i, rfl⟩ := hf
        exact (Commute.one_right _).sub_right ((hcomm j i).pow_right _)
      · have hp' : Dend j ^ p = Dend j := AddMonoidHom.ext fun c =>
          (hpow j p c).trans (derivation_iterate_char_eq_self_of_coords p x D hd hD j c)
        rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hpr.one_lt.le, hp', sub_self]
    have h0 : D j (π c) = 0 := by
      show (Dend j * π) c = 0
      rw [hz]
      rfl
    rw [h0, zero_smul]
  · intro g
    rw [hπ']
    apply list_prod_apply_fixed
    intro f hf
    rw [List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    have hDg : D i (g ^ p) = 0 := by
      rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    show g ^ p - (Dend i ^ (p - 1)) (g ^ p) = g ^ p
    rw [hpow, hm, Function.iterate_succ_apply, hDg, Function.iterate_fixed (map_zero (D i)),
      sub_zero]

end GlobalTheory.ProjFn
