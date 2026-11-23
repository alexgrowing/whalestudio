import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscPropertiesStatement

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem seq_eq_iff_modEq_of_op {K : Type*} (G : K → K → K) (τ : ℕ → K)
    (hG : ∀ i j, G (τ i) (τ j) = τ (i + j)) (q : ℕ) (hq : 0 < q) (h0 : τ q = τ 0)
    (hord : ∀ {M : Type} [AddMonoid M] (x : M), (∀ d : ℕ, d • x = 0 ↔ τ d = τ 0) →
      addOrderOf x = q) (i j : ℕ) :
    τ i = τ j ↔ i ≡ j [MOD q] := by
  have shift : ∀ a m, τ m = τ 0 → τ (a + m) = τ a := by
    intro a m hm
    rw [← hG a m, hm, hG a 0, Nat.add_zero]
  have mulS : ∀ s, τ s = τ 0 → ∀ n, τ (s * n) = τ 0 := by
    intro s hs n
    induction n with
    | zero => rw [Nat.mul_zero]
    | succ n ih => rw [Nat.mul_succ, shift _ _ hs, ih]
  have cancel : ∀ a k, τ (a + k) = τ a → τ k = τ 0 := by
    intro a k hak
    have e : (q - 1) * a + a = q * a := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.succ_le_of_lt hq)]
    calc τ k = τ (k + q * a) := (shift k _ (mulS q h0 a)).symm
      _ = G (τ (a + k)) (τ ((q - 1) * a)) := by rw [hG, ← e]; congr 1; ac_rfl
      _ = G (τ a) (τ ((q - 1) * a)) := by rw [hak]
      _ = τ (q * a) := by rw [hG, Nat.add_comm, e]
      _ = τ 0 := mulS q h0 a
  classical
  have hex : ∃ r, 0 < r ∧ τ r = τ 0 := ⟨q, hq, h0⟩
  obtain ⟨r, hr, hmin⟩ : ∃ r, (0 < r ∧ τ r = τ 0) ∧ ∀ m < r, ¬ (0 < m ∧ τ m = τ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hdvd : ∀ d, τ d = τ 0 ↔ r ∣ d := by
    intro d
    constructor
    · intro hd
      have hmod : τ (d % r) = τ 0 := by
        have h := shift (d % r) (r * (d / r)) (mulS r hr.2 _)
        rw [Nat.mod_add_div] at h
        rw [← h, hd]
      by_contra hnd
      have hpos : 0 < d % r := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
      exact hmin _ (Nat.mod_lt d hr.1) ⟨hpos, hmod⟩
    · rintro ⟨c, rfl⟩
      exact mulS r hr.2 c
  have hrq : r = q := by
    have h := hord (M := ZMod r) (1 : ZMod r) (fun d => by
      rw [nsmul_eq_mul, mul_one, CharP.cast_eq_zero_iff (ZMod r) r, hdvd])
    rwa [ZMod.addOrderOf_one] at h
  have key : ∀ d, τ d = τ 0 ↔ q ∣ d := by
    intro d; rw [hdvd, hrq]
  wlog hij : i ≤ j generalizing i j with H
  · rw [eq_comm, Nat.ModEq.comm]; exact H j i (by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.modEq_iff_dvd' hij, Nat.add_sub_cancel_left, ← key, eq_comm]
  exact ⟨cancel i k, fun h => shift i k h⟩

theorem tower_exact_order : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → (∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n)) ∧ (∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n)) ∧ ∀ n i j, ev1 (nMul F i) (t n) = ev1 (nMul F j) (t n) ↔ i ≡ j [MOD p ^ n] := by
  intro K _ _ _ p _ F hF t ht ht0 ht1 htp
  have base := (GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF).2
  have hA : ∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n) := by
    intro n j
    rw [← htp n, (base (t (n + 1)) (ht _)).2.2.2.2.1 j p, Nat.mul_comm p j]
  have hB : ∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n) := by
    intro n m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      rw [← Nat.add_assoc, pow_succ', Nat.mul_assoc, hA, ih]
  refine ⟨hA, hB, fun n i j => ?_⟩
  have hτ0 : ev1 (nMul F 0) (t n) = 0 := (base (t n) (ht n)).1
  have hpn : ev1 (nMul F (p ^ n)) (t n) = 0 := by
    have h := hB 0 n 1
    rw [Nat.mul_one, Nat.zero_add, (base (t 0) (ht 0)).2.1, ht0] at h
    exact h
  refine seq_eq_iff_modEq_of_op (fun a b => ev F.toPowerSeries ![a, b])
    (fun d => ev1 (nMul F d) (t n)) (base (t n) (ht n)).2.2.2.1 (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos n) (by simp only [hpn, hτ0]) ?_ i j
  intro M _ x hx
  have hx' : ∀ d : ℕ, d • x = 0 ↔ ev1 (nMul F d) (t n) = 0 := by
    intro d; rw [hx d]; simp only [hτ0]
  rcases n with _ | k
  · have h := (hx' 1).2 (by rw [(base (t 0) (ht 0)).2.1, ht0])
    rw [one_nsmul] at h
    subst h
    simp
  · have h1k : ev1 (nMul F (p ^ k)) (t (k + 1)) = t 1 := by
      have h := hB 1 k 1
      rw [Nat.mul_one, Nat.add_comm 1 k, (base (t 1) (ht 1)).2.1] at h
      exact h
    exact addOrderOf_eq_prime_pow (fun h => ht1 (by rw [← h1k]; exact (hx' _).1 h)) ((hx' _).2 hpn)

end GlobalTheory.ConvSer
