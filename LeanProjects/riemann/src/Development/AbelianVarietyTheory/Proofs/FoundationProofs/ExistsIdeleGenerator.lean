import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Nat

namespace GlobalTheory.IdealIdele

theorem pow_factorial_mul {M : Type} [Monoid M] [Fintype M] (a : M) (t : ℕ) (ht : 0 < t) :
    a ^ ((Fintype.card M)! * t) = a ^ (Fintype.card M)! := by
  obtain ⟨i, j, hij, hj, e⟩ : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card M ∧ a ^ i = a ^ j := by
    obtain ⟨i, j, hne, e⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card M + 1) => a ^ (i : ℕ)) (by simp)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, Nat.lt_succ_iff.1 j.2, e⟩
    · exact ⟨j, i, h, Nat.lt_succ_iff.1 i.2, e.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  have hd : 0 < d := by omega
  have key : ∀ u : ℕ, a ^ (i + d * u) = a ^ i := by
    intro u
    induction u with
    | zero => simp
    | succ u ih => rw [Nat.mul_succ, ← add_assoc, pow_add, ih, ← pow_add, ← e]
  obtain ⟨c, hc⟩ : d ∣ (Fintype.card M)! := Nat.dvd_factorial hd (by omega)
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le
    (show i ≤ (Fintype.card M)! from le_trans (by omega) (Nat.self_le_factorial _))
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  have : (Fintype.card M)! * t.succ = i + d * (c * t) + s := by
    rw [Nat.mul_succ, ← mul_assoc, ← hc]; omega
  rw [this, pow_add, key, ← pow_add, ← hs]

theorem int_dvd_pow_sub (m N t : ℕ) (hN : 0 < N) (ht : 0 < t) :
    ∃ c : ℤ, (m : ℤ) ^ (N ! * t) = (m : ℤ) ^ N ! + N * c := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h := pow_factorial_mul (m : ZMod N) t ht
  rw [ZMod.card] at h
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((m : ℤ) ^ (N ! * t) - (m : ℤ) ^ N !) N).1
    (by push_cast; rw [h, sub_self])
  exact ⟨c, by linear_combination hc⟩

section Abstract

variable {A : Type} [CommRing A] (S : Subring A)

theorem exists_idem
    (hsep : ∀ y : A, (∀ N : ℕ, 0 < N → ∃ w ∈ S, y = (N : A) * w) → y = 0)
    (hcpl : ∀ x : ℕ → A, (∀ N, x N ∈ S) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ S, x (N * m) = x N + (N : A) * w) →
      ∃ y ∈ S, ∀ N : ℕ, 0 < N → ∃ w ∈ S, y = x N + (N : A) * w)
    (m : ℕ) (hm : 0 < m) :
    ∃ f ∈ S, f * f = f ∧ (∃ w ∈ S, f = (m : A) * w) ∧
      ∀ n : ℕ, 0 < n → m.Coprime n → ∃ w ∈ S, 1 - f = (n : A) * w := by
  have hc : ∀ N t : ℕ, 0 < N → 0 < t →
      ∃ c : ℤ, (m : A) ^ (N ! * t) = (m : A) ^ N ! + N * c := fun N t hN ht => by
    obtain ⟨c, h⟩ := int_dvd_pow_sub m N t hN ht
    refine ⟨c, ?_⟩
    have := congrArg (Int.cast : ℤ → A) h
    push_cast at this
    exact this
  have hx : ∀ k : ℕ, (m : A) ^ k ∈ S := fun k => pow_mem (natCast_mem S m) k
  obtain ⟨f, hf, h⟩ := hcpl (fun N => (m : A) ^ N !) (fun N => hx _) (by
    intro N k hN hk
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right N hk)
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by
      rintro rfl
      exact (Nat.factorial_ne_zero _) (by simpa using ht))
    obtain ⟨c, hc⟩ := hc N t hN ht0
    exact ⟨c, intCast_mem S c, by simp only [ht, hc]⟩)
  refine ⟨f, hf, ?_, ?_, fun n hn hmn => ?_⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨c, hc⟩ := hc N 2 hN two_pos
    refine ⟨c + (2 * (m : A) ^ N ! * w + N * w * w - w), ?_, ?_⟩
    · exact add_mem (intCast_mem S c) (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (hx _)) hw)
        (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
    · rw [pow_mul] at hc
      rw [hh]; linear_combination hc
  · obtain ⟨w, hw, hh⟩ := h m hm
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero m)
    refine ⟨(m : A) ^ s + w, add_mem (hx s) hw, ?_⟩
    rw [hh, hs, pow_succ]; ring
  · obtain ⟨w, hw, hh⟩ := h n hn
    obtain ⟨t, ht⟩ := Nat.dvd_factorial (Nat.totient_pos.2 hn) (Nat.totient_le n)
    have h1 : m ^ n ! ≡ 1 [MOD n] := by
      have := (Nat.ModEq.pow_totient hmn).pow t
      rwa [← pow_mul, ← ht, one_pow] at this
    obtain ⟨c, hc⟩ := h1.dvd
    have hc' := congrArg (Int.cast : ℤ → A) hc
    push_cast at hc'
    refine ⟨c - w, sub_mem (intCast_mem S c) hw, ?_⟩
    rw [hh]; linear_combination hc'

end Abstract

theorem exists_local_generator {E : Type} [Field E] [NumberField E] (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    ∃ (m n : ℕ) (β : 𝓞 E), 0 < m ∧ 0 < n ∧ m.Coprime n ∧ (m : 𝓞 E) ∈ B ∧ β ∈ B ∧ β ≠ 0 ∧
      ∀ b ∈ B, β ∣ (n : 𝓞 E) * b := by
  set m := 2 * Ideal.absNorm B with hm
  have hN : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hB)
  have hm2 : 2 ≤ m := by omega
  have hmB : (m : 𝓞 E) ∈ B := by
    rw [hm, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem B)
  have hm0 : (m : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨β, hβ⟩ := IsDedekindDomain.exists_sup_span_eq (I := B * Ideal.span {(m : 𝓞 E)}) (J := B)
    Ideal.mul_le_left (mul_ne_zero hB (by simpa using hm0))
  have hβB : β ∈ B := hβ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self β)
  obtain ⟨C, hC⟩ : B ∣ Ideal.span {β} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hβB)
  have hsup : Ideal.span {(m : 𝓞 E)} ⊔ C = ⊤ := by
    apply mul_left_cancel₀ hB
    rw [Ideal.mul_sup, ← hC, hβ, Ideal.mul_top]
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq, Ideal.span_singleton_eq_top] at hsup
    have h1 := Ideal.absNorm_eq_one_iff.2 (Ideal.span_singleton_eq_top.2 hsup)
    rw [Ideal.absNorm_span_natCast] at h1
    have h2 := (Nat.pow_eq_one.1 h1).resolve_left (by omega)
    exact Module.finrank_pos.ne' h2
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hB hC0 (by rw [← hC]; simp)
  haveI : Finite (𝓞 E ⧸ C) := Ideal.finiteQuotientOfFreeOfNeBot C hC0
  have hu : IsUnit (Ideal.Quotient.mk C (m : 𝓞 E)) := by
    obtain ⟨x, hx, c, hc, e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk C a) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk C), Ideal.Quotient.eq]
    rw [show (m : 𝓞 E) * a - 1 = -c by linear_combination e]
    exact neg_mem hc
  obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hu.unit)
  have e' : (m : 𝓞 E) ^ k - 1 ∈ C := by
    rw [← Ideal.Quotient.eq, map_pow, map_one]
    simpa using congrArg Units.val e
  have h1 : 1 < m ^ k := Nat.one_lt_pow hk.ne' (by omega)
  refine ⟨m, m ^ k - 1, β, by omega, by omega, ?_, hmB, hβB, hβ0, fun b hb => ?_⟩
  · refine Nat.Coprime.of_dvd_left (dvd_pow_self m hk.ne') ?_
    exact (Nat.coprime_self_sub_right h1.le).2 (Nat.coprime_one_right _)
  · rw [← Ideal.mem_span_singleton, hC, mul_comm (((m ^ k - 1 : ℕ)) : 𝓞 E)]
    refine Ideal.mul_mem_mul hb ?_
    rw [Nat.cast_sub h1.le]
    push_cast
    exact e'

theorem exists_idele_generator : ∀ (D : D7) (B : Ideal (𝓞 D.host.E)), B ≠ ⊥ → ∃ y : (AE D)ˣ, (∀ b ∈ B, ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (b : D.host.E) ∈ OhE D) ∧ ∃ (k : ℕ) (b : Fin k → 𝓞 D.host.E) (w : Fin k → AE D), (∀ i, b i ∈ B) ∧ (∀ i, w i ∈ OhE D) ∧ (y : AE D) = ∑ i, inc D (b i : D.host.E) * w i := by
  intro D B hB
  obtain ⟨m, n, β, hm, hn, hmn, hmB, hβB, hβ0, hdvd⟩ := exists_local_generator B hB
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := exists_idem (OhE D) hsep hcpl m hm
  obtain ⟨v, hv, hfv⟩ := h3 n hn hmn
  have hint : ∀ b : 𝓞 D.host.E, inc D (b : D.host.E) ∈ OhE D := fun b =>
    (GlobalTheory.HeckeVal.inc_mem_iff D _).2 b.isIntegral_coe
  have hβE : (β : D.host.E) ≠ 0 := by simpa using hβ0
  have hinv : inc D (β : D.host.E) * inc D (β : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hβE, map_one]
  have hy : ((1 - f) * inc D (β : D.host.E) + f) * ((1 - f) * inc D (β : D.host.E)⁻¹ + f) = 1 := by
    linear_combination (1 - f) ^ 2 * hinv +
      (2 - inc D (β : D.host.E) - inc D (β : D.host.E)⁻¹) * hff
  refine ⟨⟨_, _, hy, by rw [mul_comm, hy]⟩, fun b hb => ?_, 2, ![β, m], ![1 - f, w], ?_, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hdvd b hb
    have hd' : (n : AE D) * inc D (b : D.host.E) = inc D (β : D.host.E) * inc D (d : D.host.E) := by
      rw [← map_natCast (inc D), ← map_mul, ← map_mul]
      congr 1
      exact_mod_cast congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hd
    change ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) ∈ OhE D
    rw [show ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) =
      v * inc D (d : D.host.E) + f * inc D (b : D.host.E) by
        rw [hfv]
        linear_combination v * inc D (β : D.host.E)⁻¹ * hd' + v * inc D (d : D.host.E) * hinv]
    exact add_mem (mul_mem hv (hint d)) (mul_mem hf (hint b))
  · intro i
    fin_cases i
    · exact hβB
    · exact hmB
  · intro i
    fin_cases i
    · exact sub_mem (one_mem _) hf
    · exact hw
  · have : inc D (((m : 𝓞 D.host.E)) : D.host.E) = (m : AE D) := by
      rw [← map_natCast (inc D)]; congr 1
    change (1 - f) * inc D (β : D.host.E) + f = _
    rw [Fin.sum_univ_two]
    change _ = inc D (β : D.host.E) * (1 - f) + inc D (((m : 𝓞 D.host.E)) : D.host.E) * w
    rw [this, ← hfw]; ring

end GlobalTheory.IdealIdele
