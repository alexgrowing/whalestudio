import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LeOfOneLeMul
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickDefs

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Reals

theorem natlog_le_three (p M : ℕ) (a : ℝ) (hp : 2 ≤ p) (ha : 1 ≤ a) (hM : (M : ℝ) ≤ a ^ 3) :
    ((Nat.log p M : ℕ) : ℝ) ≤ 3 * Real.logb p a := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hℓ : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 ha
  by_cases h0 : M = 0
  · subst h0
    simp only [Nat.log_zero_right, Nat.cast_zero]
    linarith
  · have hpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have l1 : ((Nat.log p M : ℕ) : ℝ) ≤ Real.logb p (M : ℝ) := Real.natLog_le_logb _ _
    have l2 : Real.logb p (M : ℝ) ≤ Real.logb p (a ^ 3) := Real.logb_le_logb_of_le hp1 hpos hM
    have l3 : Real.logb p (a ^ 3) = 3 * Real.logb p a := by rw [Real.logb_pow]; norm_num
    linarith

theorem two_a_le_cube (a : ℝ) (h : 2 ≤ a) : 2 * a ≤ a ^ 3 := by nlinarith [sq_nonneg a]

theorem sq_add_le_cube (a : ℝ) (h : 2 ≤ a) : a ^ 2 + a ≤ a ^ 3 := by nlinarith [sq_nonneg a]

theorem four_N_a (N a : ℝ) (ha : 0 ≤ a) (h : 4 * N ≤ a) : 2 * (N * (2 * a)) ≤ a ^ 2 := by nlinarith

theorem size_fin (N k r K ℓ A B Cc : ℝ) (hN : 0 ≤ N) (hℓ : 0 ≤ ℓ) (hk : 1 ≤ k) (hr0 : 0 ≤ r) (hK0 : 0 ≤ K) (hr : r ≤ k)
    (hK : K ≤ k)
    (hA : A ≤ 2 * N * (k ^ 2 * (3 * ℓ))) (hB : B ≤ N * (r * (3 * ℓ))) (hC : Cc ≤ N * (K * (3 * ℓ))) :
    A + B / 2 + Cc / 2 ≤ 9 * (N * k ^ 2 * ℓ) := by
  have h1 : k ≤ k ^ 2 := le_sq_of_one_le k hk
  have h2 : 0 ≤ N * ℓ := mul_nonneg hN hℓ
  have h3 : (N * ℓ) * r ≤ (N * ℓ) * k ^ 2 := mul_le_mul_of_nonneg_left (le_trans hr h1) h2
  have h4 : (N * ℓ) * K ≤ (N * ℓ) * k ^ 2 := mul_le_mul_of_nonneg_left (le_trans hK h1) h2
  nlinarith

theorem sl_lt_real (B Y k : ℝ) (s : ℤ) (hs : s = ⌊B / (Y * k ^ 2)⌋) (hB : 0 < B) (hY : 2 ≤ Y) (hk : 1 ≤ k) :
    3 / 8 * (s : ℝ) < B / 2 := by
  have h1 : (s : ℝ) ≤ B / (Y * k ^ 2) := by rw [hs]; exact Int.floor_le _
  have h2 : (2 : ℝ) ≤ Y * k ^ 2 := by
    have : (1 : ℝ) ≤ k ^ 2 := one_le_pow₀ hk
    nlinarith
  have h3 : B / (Y * k ^ 2) ≤ B / 2 := div_le_div_of_nonneg_left hB.le (by norm_num) h2
  linarith

end Reals

section Mult

theorem mult_level (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] {n : ℕ} (d : ι → ℕ) (be : ι × Fin n →₀ ℕ)
    (hbe : ∀ x, multideg be x = d x) :
    padicValNat p (∏ x, (d x).factorial) ≤ padicValNat p (expFact be) + ∑ x, n * Nat.log p (d x) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin n => be (s, c)) *
      ∏ c : Fin n, (be (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hbe s]
    rfl
  have h2 : expFact be = ∏ s : ι, ∏ c : Fin n, (be (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin n => be (s, c))) * expFact be := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin n => be (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact be ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  have h4 : padicValNat p (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin n => be (s, c))) ≤
      ∑ x, n * Nat.log p (d x) := by
    rw [Formalism.CountingSumsFrames.fock_val_prod p _ _ (fun s _ => (Nat.multinomial_pos _ _).ne')]
    refine Finset.sum_le_sum fun s _ => ?_
    have := Formalism.CountingSumsFrames.fock_mult_val_le p (fun c : Fin n => be (s, c)) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at this
    have e : ∑ c : Fin n, be (s, c) = d s := hbe s
    rw [e] at this
    exact this
  rw [h3, padicValNat.mul hMn0 hE0]
  omega

theorem mult_level_real (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] {n : ℕ} (d : ι → ℕ) (be : ι × Fin n →₀ ℕ)
    (hbe : ∀ x, multideg be x = d x) (N : ℕ) (a : ℝ) (ha : 2 ≤ a) (hcard : Fintype.card ι ≤ N)
    (hd : ∀ x, (d x : ℝ) ≤ 2 * a) :
    (padicValNat p (∏ x, (d x).factorial) : ℝ) - (padicValNat p (expFact be) : ℝ) ≤
      (N : ℝ) * ((n : ℝ) * (3 * Real.logb p a)) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hℓ : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 (by linarith)
  have h := mult_level p d be hbe
  have h' : (padicValNat p (∏ x, (d x).factorial) : ℝ) ≤
      (padicValNat p (expFact be) : ℝ) + ((∑ x, n * Nat.log p (d x) : ℕ) : ℝ) := by exact_mod_cast h
  have hs : ((∑ x, n * Nat.log p (d x) : ℕ) : ℝ) ≤ (N : ℝ) * ((n : ℝ) * (3 * Real.logb p a)) := by
    push_cast
    calc ∑ x, (n : ℝ) * ((Nat.log p (d x) : ℕ) : ℝ) ≤ ∑ _x : ι, (n : ℝ) * (3 * Real.logb p a) := by
          refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact natlog_le_three p _ a hp2 (by linarith) (le_trans (hd x) (two_a_le_cube a ha))
      _ = (Fintype.card ι : ℝ) * ((n : ℝ) * (3 * Real.logb p a)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((n : ℝ) * (3 * Real.logb p a)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  linarith

end Mult

section Dno

variable {r K J : ℕ} [NeZero J]

theorem degIn_le_sum {ι : Type} [Fintype ι] (d : ι → ℕ) (S : Set ι) : degIn d S ≤ ∑ x, d x := by
  unfold degIn
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem triangular_count_le_sq (K k : ℕ) (hK : K ≤ k) : N0 K ≤ k ^ 2 := by
  unfold N0
  calc K * (K - 1) / 2 ≤ K * (K - 1) := Nat.div_le_self _ _
    _ ≤ K * K := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤ k * k := Nat.mul_le_mul hK hK
    _ = k ^ 2 := by ring

theorem card_idx (nL : ZMod J → ℕ) :
    Fintype.card (Σ j : ZMod J, Fin (nL j + r + 1)) = Fintype.card (TL J nL r) + J := by
  rw [card_TL_eq, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]

theorem J_le_card (nL : ZMod J → ℕ) (hr : 1 ≤ r) : J ≤ Fintype.card (TL J nL r) := by
  rw [card_TL_eq]
  calc J = ∑ _j : ZMod J, 1 := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]
    _ ≤ ∑ j : ZMod J, (nL j + r) := Finset.sum_le_sum fun j _ => by omega

theorem DnoOf_le (p : ℕ) (hp : 2 ≤ p) (nL : ZMod J → ℕ) (dNo : TL J nL r → ℕ) (N k : ℕ) (a : ℝ) (hr : 1 ≤ r)
    (hK : K ≤ k) (hcard : Fintype.card (TL J nL r) ≤ N) (hd : ∀ x, (dNo x : ℝ) ≤ 2 * a) (ha2 : 2 ≤ a)
    (h4N : 4 * (N : ℝ) ≤ a) (hka : (k : ℝ) ≤ a) :
    (DnoOf (K := K) p nL dNo : ℝ) ≤ 2 * (N : ℝ) * ((k : ℝ) ^ 2 * (3 * Real.logb p a)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hℓ : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 (by linarith)
  have hcard' : (Fintype.card (TL J nL r) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
  have hsum : ((∑ x, dNo x : ℕ) : ℝ) ≤ (N : ℝ) * (2 * a) := by
    push_cast
    calc ∑ x, (dNo x : ℝ) ≤ ∑ _x : TL J nL r, 2 * a := Finset.sum_le_sum fun x _ => hd x
      _ = (Fintype.card (TL J nL r) : ℝ) * (2 * a) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (2 * a) := mul_le_mul_of_nonneg_right hcard' (by linarith)
  have hterm : ∀ i : Σ j : ZMod J, Fin (nL j + r + 1),
      ((N0 K * Nat.log p (2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1) : ℕ) : ℝ) ≤
        (k : ℝ) ^ 2 * (3 * Real.logb p a) := by
    intro i
    have hM : ((2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1 : ℕ) : ℝ) ≤ a ^ 3 := by
      have e1 : 2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1 ≤ 2 * (∑ x, dNo x) + k := by
        have := degIn_le_sum dNo (NSet nL i.1 i.2.val)
        omega
      have e2 : ((2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1 : ℕ) : ℝ) ≤ ((2 * (∑ x, dNo x) + k : ℕ) : ℝ) := by
        exact_mod_cast e1
      have e3 : ((2 * (∑ x, dNo x) + k : ℕ) : ℝ) = 2 * ((∑ x, dNo x : ℕ) : ℝ) + (k : ℝ) := by push_cast; ring
      have e4 := four_N_a (N : ℝ) a (by linarith) h4N
      have e5 := sq_add_le_cube a ha2
      rw [e3] at e2
      linarith
    have l := natlog_le_three p _ a hp (by linarith) hM
    have hN0 : ((N0 K : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast triangular_count_le_sq K k hK
    rw [Nat.cast_mul]
    exact mul_le_mul hN0 l (Nat.cast_nonneg _) (by positivity)
  have hidx : (Fintype.card (Σ j : ZMod J, Fin (nL j + r + 1)) : ℝ) ≤ 2 * (N : ℝ) := by
    have h1 := card_idx (r := r) nL
    have h2 := J_le_card (r := r) nL hr
    have : Fintype.card (Σ j : ZMod J, Fin (nL j + r + 1)) ≤ 2 * N := by omega
    exact_mod_cast this
  unfold DnoOf
  rw [Nat.cast_sum]
  calc ∑ i : Σ j : ZMod J, Fin (nL j + r + 1),
        ((N0 K * Nat.log p (2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1) : ℕ) : ℝ)
      ≤ ∑ _i : Σ j : ZMod J, Fin (nL j + r + 1), (k : ℝ) ^ 2 * (3 * Real.logb p a) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card (Σ j : ZMod J, Fin (nL j + r + 1)) : ℝ) * ((k : ℝ) ^ 2 * (3 * Real.logb p a)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 * (N : ℝ) * ((k : ℝ) ^ 2 * (3 * Real.logb p a)) := mul_le_mul_of_nonneg_right hidx (by positivity)

end Dno

end Formalism.MainNotions.Proposition5Numerics
