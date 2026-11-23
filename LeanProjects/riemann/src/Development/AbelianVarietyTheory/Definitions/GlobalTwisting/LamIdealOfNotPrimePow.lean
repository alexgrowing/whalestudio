import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero

noncomputable section

open Finset ArithmeticFunction NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.Hk

structure LFam where

  G : Type
  [ag : AddCommGroup G]
  [ft : Fintype G]

  B : ℝ

  κ : ℝ

  a : G → ℕ → ℝ

  lam : G → ℕ → ℝ
  B_ge : 4 ≤ B
  card_le : (Fintype.card G : ℝ) ≤ B
  κ_ge : 1 / B ≤ κ
  κ_le : κ ≤ 4
  a_nonneg : ∀ g n, 0 ≤ a g n
  a_zero : ∀ g, a g 0 = 0
  a_one : a 0 1 = 1
  a_one_ne : ∀ g, g ≠ 0 → a g 1 = 0
  count : ∀ (g : G) (x : ℝ), 1 ≤ x → |∑ n ∈ Icc 1 ⌊x⌋₊, a g n - κ * x| ≤ 10 * Real.sqrt x
  theta : ∀ (g : G) (t : ℝ), 0 < t → t ≤ 1 → |∑' n : ℕ, a g n * Real.exp (-(t * n)) - κ / t| ≤ B ^ 10 * t
  lam_nonneg : ∀ g n, 0 ≤ lam g n
  lam_le : ∀ n, ∑ g, lam g n ≤ 2 * Λ n
  conv : ∀ g n, a g n * Real.log n = ∑ h, ∑ p ∈ n.divisorsAntidiagonal, lam h p.1 * a (g - h) p.2
  sq : ∀ χ : AddChar G ℂ, χ * χ = 1 → ∀ n : ℕ,
    0 ≤ ∑ p ∈ n.divisorsAntidiagonal, (∑ g, a g p.1) * ∑ g, (χ g).re * a g p.2 ∧
    ∑ g, a g n ≤ ∑ p ∈ (n ^ 2).divisorsAntidiagonal, (∑ g, a g p.1) * ∑ g, (χ g).re * a g p.2

attribute [instance] LFam.ag LFam.ft

namespace LFam

variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)

def aChi (n : ℕ) : ℂ := ∑ g, χ g * (𝓕.a g n : ℂ)

def lamChi (n : ℕ) : ℂ := ∑ g, χ g * (𝓕.lam g n : ℂ)

open Classical in

def res : ℂ := if χ = 1 then ((𝓕.κ * Fintype.card 𝓕.G : ℝ) : ℂ) else 0

def mel (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), ((∑ n ∈ Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x) * (x : ℂ) ^ (-s - 1)

open Classical in

def F (s : ℂ) : ℂ := if χ = 1 then 𝓕.res χ * s + (s - 1) * s * 𝓕.mel χ s else s * 𝓕.mel χ s

def psi (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, 𝓕.lamChi χ n

def ell (t : ℝ) : ℝ := Real.log (𝓕.B * (|t| + 2))

def ExcZ (c : ℝ) (Z : Finset ℝ) : Prop :=
  Z.card ≤ 1 ∧ (∀ β ∈ Z, 1 - c / 𝓕.ell 0 ≤ β ∧ β < 1 ∧ 𝓕.F χ β = 0 ∧ deriv (𝓕.F χ) β ≠ 0) ∧
    ∀ s : ℂ, 1 - c / 𝓕.ell s.im ≤ s.re → 𝓕.F χ s = 0 → ∃ β ∈ Z, s = (β : ℂ)

theorem two_lt_ell (t : ℝ) : 2 < 𝓕.ell t := by
  have hB := 𝓕.B_ge
  have ht := abs_nonneg t
  have h8 : (8 : ℝ) ≤ 𝓕.B * (|t| + 2) := by nlinarith
  have h2 := Real.log_two_gt_d9
  have e : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := Real.log_le_log (by norm_num) h8
  unfold ell
  linarith

theorem half_lt_re_of_region {c : ℝ} (hc : c ≤ 1) {s : ℂ} (hs : 1 - c / 𝓕.ell s.im ≤ s.re) : 1 / 2 < s.re := by
  have h := 𝓕.two_lt_ell s.im
  have : c / 𝓕.ell s.im < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  linarith

end LFam

section Ray

variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : GlobalTheory.Mem.RayData K M)

def idealsIn (g : D.G) (n : ℕ) : Set (Ideal (𝓞 K)) :=
  {I | I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = g}

open Classical in

def lamIdeal (I : Ideal (𝓞 K)) : ℝ :=
  if ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k then Real.log (Ideal.absNorm I.radical) else 0

def aRay (g : D.G) (n : ℕ) : ℝ := ((idealsIn D g n).ncard : ℝ)

def lamRay (g : D.G) (n : ℕ) : ℝ := ∑ᶠ I ∈ idealsIn D g n, lamIdeal I

namespace RayCount

theorem idealsIn_finite (g : D.G) (n : ℕ) : (idealsIn D g n).Finite :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset fun _ h => h.2.2.1

theorem coe_aRay_eq_cnt (g : D.G) {n : ℕ} (hn : n ≠ 0) : (aRay D g n : ℂ) = D.cnt g n := by
  rw [D.cnt_of_ne_zero g hn, aRay, ← Nat.card_coe_set_eq]
  norm_cast
  exact Nat.card_congr (Equiv.subtypeEquivRight fun I => by simp only [idealsIn, Set.mem_setOf_eq]; tauto)

theorem aRay_eq_card (g : D.G) (n : ℕ) : aRay D g n = ((idealsIn_finite D g n).toFinset.card : ℝ) := by
  rw [aRay, Set.ncard_eq_toFinset_card _ (idealsIn_finite D g n)]

theorem lamRay_eq_sum (g : D.G) (n : ℕ) : lamRay D g n = ∑ I ∈ (idealsIn_finite D g n).toFinset, lamIdeal I :=
  finsum_mem_eq_finite_toFinset_sum _ (idealsIn_finite D g n)

theorem lamIdeal_prime_pow (P : Ideal (𝓞 K)) (hP : P.IsPrime) (h0 : P ≠ ⊥) (k : ℕ) (hk : 1 ≤ k) :
    lamIdeal (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [lamIdeal, if_pos ⟨P, k, hP, h0, hk, rfl⟩, Ideal.radical_pow _ (by omega), hP.radical]

theorem lamIdeal_of_not_prime_pow {I : Ideal (𝓞 K)}
    (h : ¬ ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k) : lamIdeal I = 0 := by
  rw [lamIdeal, if_neg h]

theorem lamIdeal_unit : lamIdeal (⊤ : Ideal (𝓞 K)) = 0 := by
  unfold lamIdeal; split_ifs <;> simp

end RayCount

end Ray

def qForm (α γ l θ₁ θ₂ : ℝ) (v : ℤ × ℤ) : ℝ := α * (v.1 + θ₁ + l * v.2) ^ 2 + γ * (v.2 + θ₂) ^ 2

namespace OddFam

def ao (n : ℕ) : ℝ := if Odd n then 1 else 0

theorem ao_nonneg (n : ℕ) : 0 ≤ ao n := by unfold ao; split_ifs <;> norm_num

theorem count_odd (N : ℕ) : |∑ n ∈ Icc 1 N, ao n - N / 2| ≤ 1 / 2 := by
  have : ∀ N : ℕ, ∑ n ∈ Icc 1 N, ao n = N / 2 + ao N / 2 := by
    intro N
    induction N with
    | zero => simp [ao]
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      unfold ao
      by_cases h : Odd k
      · have : ¬ Odd (k+1) := by rw [Nat.odd_add_one]; simpa using h
        simp [h, this]; ring
      · have : Odd (k+1) := by rw [Nat.odd_add_one]; simpa using h
        simp [h, this]; ring
  rw [this]; unfold ao; split_ifs <;> simp [abs_le] <;> norm_num

theorem tsum_odd (t : ℝ) (ht : 0 < t) :
    ∑' n : ℕ, ao n * Real.exp (-(t * n)) = Real.exp (-t) / (1 - Real.exp (-t) ^ 2) := by
  have h1 : Real.exp (-t) < 1 := by simpa using ht
  have h0 := Real.exp_pos (-t)
  have hq : Real.exp (-t) ^ 2 < 1 := by nlinarith
  have ho : HasSum (fun k : ℕ => ao (2 * k + 1) * Real.exp (-(t * ((2 * k + 1 : ℕ) : ℝ))))
      (Real.exp (-t) * (1 - Real.exp (-t) ^ 2)⁻¹) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hq).mul_left (Real.exp (-t))
    have e : (fun k : ℕ => ao (2 * k + 1) * Real.exp (-(t * ((2 * k + 1 : ℕ) : ℝ)))) =
        fun i : ℕ => Real.exp (-t) * (Real.exp (-t) ^ 2) ^ i := by
      funext k
      rw [← pow_mul, ← pow_succ', ← Real.exp_nat_mul]
      simp [ao]; ring
    rw [e]; exact this
  have he : HasSum (fun k : ℕ => ao (2 * k) * Real.exp (-(t * ((2 * k : ℕ) : ℝ)))) 0 := by
    have e : (fun k : ℕ => ao (2 * k) * Real.exp (-(t * ((2 * k : ℕ) : ℝ)))) = fun _ : ℕ => (0 : ℝ) := by
      funext k
      have : ¬ Odd (2 * k) := by simp
      simp only [ao, if_neg this, zero_mul]
    rw [e]; exact hasSum_zero
  have := HasSum.even_add_odd (f := fun n : ℕ => ao n * Real.exp (-(t * n))) he ho
  rw [this.tsum_eq]; simp [div_eq_mul_inv]

theorem sinh_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    |Real.exp (-t) / (1 - Real.exp (-t) ^ 2) - (1 / 2) / t| ≤ 4 ^ 10 * t := by
  have hs : Real.exp (-t) / (1 - Real.exp (-t) ^ 2) = (1 / 2) / Real.sinh t := by
    have h1 : Real.exp (-t) < 1 := by simpa using ht
    have h0 := Real.exp_pos (-t)
    have hq : 0 < 1 - Real.exp (-t) ^ 2 := by nlinarith
    have hp : 0 < Real.sinh t := Real.sinh_pos_iff.2 ht
    have e : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    rw [div_eq_div_iff hq.ne' hp.ne', Real.sinh_eq]; nlinarith
  have hl : t ≤ Real.sinh t := Real.self_le_sinh_iff.2 ht.le
  have hu : Real.sinh t ≤ t + t ^ 3 := by
    have a := Real.exp_bound (x := t) (by rw [abs_of_pos ht]; exact h1) (n := 3) (by norm_num)
    have b := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_pos ht]; exact h1) (n := 3) (by norm_num)
    simp [Finset.sum_range_succ, abs_of_pos ht, Nat.factorial] at a b
    rw [abs_le] at a b
    rw [Real.sinh_eq]
    have : 0 < t ^ 3 := by positivity
    nlinarith [a.2, b.1]
  have hp : 0 < Real.sinh t := by linarith
  rw [hs, abs_le]
  constructor
  · have : (1 / 2) / t - (1 / 2) / Real.sinh t ≤ t := by
      rw [div_sub_div _ _ ht.ne' hp.ne', div_le_iff₀ (by positivity)]
      have : t * (t * t) ≤ t * (t * Real.sinh t) := by gcongr
      nlinarith [pow_pos ht 3]
    nlinarith
  · have : (1 / 2) / Real.sinh t ≤ (1 / 2) / t := by gcongr
    nlinarith

def fam : LFam where
  G := ZMod 1
  B := 4
  κ := 1 / 2
  a _ n := ao n
  lam _ n := ao n * Λ n
  B_ge := le_rfl
  card_le := by simp
  κ_ge := by norm_num
  κ_le := by norm_num
  a_nonneg _ n := ao_nonneg n
  a_zero _ := by simp [ao]
  a_one := by simp [ao]
  a_one_ne g h := (h (Subsingleton.elim _ _)).elim
  count _ x hx := by
    have h := abs_le.1 (count_odd ⌊x⌋₊)
    have h1 := Nat.floor_le (show 0 ≤ x by linarith)
    have h2 := Nat.lt_floor_add_one x
    have h3 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  theta _ t ht h1 := by rw [tsum_odd t ht]; exact sinh_bound t ht h1
  lam_nonneg _ n := mul_nonneg (ao_nonneg n) vonMangoldt_nonneg
  lam_le n := by
    have := @vonMangoldt_nonneg n
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, one_smul]
    unfold ao; split_ifs <;> linarith
  conv _ n := by
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, one_smul]
    have : ∀ p ∈ n.divisorsAntidiagonal, ao p.1 * Λ p.1 * ao p.2 = ao n * Λ p.1 := by
      intro p hp
      rw [← (Nat.mem_divisorsAntidiagonal.1 hp).1]
      unfold ao
      by_cases h1 : Odd p.1 <;> by_cases h2 : Odd p.2 <;> simp [h1, h2, Nat.odd_mul]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Nat.sum_divisorsAntidiagonal (fun a _ => Λ a), vonMangoldt_sum]
  sq χ _ n := by
    have hχ : ∀ g : ZMod 1, (χ g).re = 1 := fun g => by rw [Subsingleton.elim g 0]; simp
    simp only [hχ, Finset.sum_const, Finset.card_univ, ZMod.card, one_smul, one_mul]
    refine ⟨Finset.sum_nonneg fun p _ => mul_nonneg (ao_nonneg _) (ao_nonneg _), ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ao]
    · have hm : (n, n) ∈ (n ^ 2).divisorsAntidiagonal := by simp [hn, sq]
      refine le_trans ?_ (Finset.single_le_sum (f := fun p : ℕ × ℕ => ao p.1 * ao p.2)
        (fun p _ => mul_nonneg (ao_nonneg _) (ao_nonneg _)) hm)
      unfold ao; split_ifs <;> simp

theorem aChi_fam (n : ℕ) : fam.aChi 1 n = if Odd n then 1 else 0 := by
  have : ∑ g : ZMod 1, (1 : AddChar (ZMod 1) ℂ) g * (ao n : ℂ) = if Odd n then 1 else 0 := by
    unfold ao; split_ifs <;> simp
  exact this

theorem res_fam : fam.res 1 = 1 / 2 := by
  have : (((1 / 2 : ℝ) * Fintype.card (ZMod 1) : ℝ) : ℂ) = 1 / 2 := by simp
  rw [LFam.res, if_pos rfl]
  exact this

end OddFam

instance : Nonempty LFam := ⟨OddFam.fam⟩

example : OddFam.fam.F 1 1 = 1 / 2 := by
  rw [LFam.F, if_pos rfl, OddFam.res_fam]; simp

example : OddFam.fam.lam 0 3 = Real.log 3 ∧ OddFam.fam.lam 0 2 = 0 := by
  constructor
  · change OddFam.ao 3 * Λ 3 = _
    rw [vonMangoldt_apply_prime Nat.prime_three, OddFam.ao, if_pos (by decide)]; simp
  · change OddFam.ao 2 * Λ 2 = _
    rw [OddFam.ao, if_neg (by decide)]; simp

example : qForm 2 3 (1 / 2) (1 / 3) (1 / 4) (1, -2) = 2 * (1 / 3) ^ 2 + 3 * (7 / 4) ^ 2 := by
  simp only [qForm]; norm_num

end GlobalTheory.Hk

end
