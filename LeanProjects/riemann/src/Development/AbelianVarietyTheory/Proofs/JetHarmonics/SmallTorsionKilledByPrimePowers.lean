import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeCoordAddAndComplexMulStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallPointMultiplicativeCoordinateExistsUniqueStatement

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.SmallTors

variable {q : ℕ} [hq : Fact q.Prime]

lemma norm_zc' (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap']
  rfl

lemma norm_nat_coprime {m : ℕ} (hm : Nat.Coprime m q) : ‖(m : ℂ_[q])‖ = 1 := by
  have h0 : (m : ℂ_[q]) = zc (m : ℤ_[q]) := by simp [zc]
  rw [h0, norm_zc']
  have h1 : ¬ ‖((m : ℤ) : ℤ_[q])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    have := (Nat.Prime.coprime_iff_not_dvd hq.out).1 hm.symm
    exact_mod_cast this
  push_cast at h1
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h1)

lemma norm_q_pow (n : ℕ) : ‖((q : ℂ_[q])) ^ n‖ = (q : ℝ) ^ (-(n : ℤ)) := by
  have h0 : (q : ℂ_[q]) ^ n = zc ((q : ℤ_[q]) ^ n) := by simp [zc]
  rw [h0, norm_zc', PadicInt.norm_p_pow]

lemma norm_eq_one {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) : ‖ξ‖ = 1 := by
  have : ξ = (ξ - 1) + 1 := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne), norm_one]
  exact max_eq_right h.le

lemma norm_pow_sub_one {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) (n : ℕ) : ‖ξ ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ξ ^ (n + 1) - 1 = ξ * (ξ ^ n - 1) + (ξ - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
    rw [norm_mul, norm_eq_one h, one_mul]; exact ih

lemma norm_geom_sub {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, ξ ^ i - n‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ∑ i ∈ Finset.range (n + 1), ξ ^ i - ((n + 1 : ℕ) : ℂ_[q])
        = (∑ i ∈ Finset.range n, ξ ^ i - n) + (ξ ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (norm_pow_sub_one h n))

lemma eq_one_of_pow {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) {m : ℕ} (hm : Nat.Coprime m q) (h1 : ξ ^ m = 1) :
    ξ = 1 := by
  have h2 := geom_sum_mul ξ m
  rw [h1, sub_self, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · have h3 := norm_geom_sub h m
    rw [h2, zero_sub, norm_neg, norm_nat_coprime hm] at h3
    exact absurd h3 (lt_irrefl _)
  · exact sub_eq_zero.1 h2

lemma inOK_int (d : ℕ) (k : ℤ) : InOK d (k : ℂ) := ⟨k, 0, by simp⟩

lemma inOK_of_eq {d : ℕ} {x y : ℂ} (h : InOK d x) (e : x = y) : InOK d y := e ▸ h

end GlobalTheory.MomOne.SmallTors

namespace GlobalTheory.MomOne
open SmallTors

theorem smallTors : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → (∀ p p', M.Small p → M.Small p' → M.Small (p + p') ∧ M.Small (-p)) ∧ (∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]), ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧ ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p)) ∧ (∀ p, PrimeTo d q p → M.Small p → InOK d p) ∧ ∀ (p α s : ℂ), InOK d α → α ≠ 0 → PrimeTo d q s → InOK d (α * p + s - 1 / 2) → M.Small p → q ≠ 2 ∧ InOK d (s - 1 / 2) := by
  intro d q hq M ω hd hd16 hsp hL hM
  obtain ⟨hadd, hcm⟩ := GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω hM
  obtain ⟨hex, hex', huniq, hlat, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω hM
  obtain ⟨⟨-, -, hring⟩, halg, -, -, hhalf, -, -⟩ := okArith d q M.ι hd hd16 hsp
  have iadd : ∀ {a b}, InOK d a → InOK d b → InOK d (a + b) := fun ha hb => (hring _ _ ha hb).1
  have imul : ∀ {a b}, InOK d a → InOK d b → InOK d (a * b) := fun ha hb => (hring _ _ ha hb).2.1
  have iconj : ∀ {a}, InOK d a → InOK d (conj a) := fun ha => (hring _ _ ha ha).2.2.2
  have one_iff : ∀ p, M.At ω 1 p ↔ InOK d p := by
    intro p
    rw [hlat 1 0 p h10, zero_sub, neg_mem_iff, hL]
  have hpow : ∀ ζ p (N : ℕ), M.At ω ζ p → M.At ω (ζ ^ N) ((N : ℂ) * p) := by
    intro ζ p N h
    induction N with
    | zero => simpa using h10
    | succ N ih =>
      have := hadd _ _ _ _ ih h
      rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact this
  have htors : ∀ ζ p (N : ℕ), M.At ω ζ p → InOK d ((N : ℂ) * p) → ζ ^ N = 1 :=
    fun ζ p N h hN => huniq _ _ _ (hpow ζ p N h) ((one_iff _).2 hN)
  have h2 : ∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]),
      ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧
        ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p) := by
    intro p N hN hNp hp
    obtain ⟨ζ, hζ⟩ := hex' p hp
    obtain ⟨n, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.out.ne_one
    have hm' : Nat.Coprime m q := ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hm).symm
    have hz : ζ ^ (q ^ n) = 1 := by
      refine eq_one_of_pow (norm_pow_sub_one hζ.2.1 _) hm' ?_
      rw [← pow_mul]; exact htors _ _ _ hζ hNp
    refine ⟨n, ζ, hz, hζ, fun α hα hn => ?_⟩
    obtain ⟨⟨a, ha⟩, -⟩ := halg α hα
    have := hcm α a n 0 ζ p (fun l hl => (hL _).2 (imul hα ((hL _).1 hl))) ha
      (by rw [ha, norm_zc'] at hn; simpa using hn) hz hζ
    rw [pow_zero] at this
    exact (one_iff _).1 this
  refine ⟨?_, h2, ?_, ?_⟩
  · intro p p' hp hp'
    obtain ⟨ζ, hζ⟩ := hex' p hp
    obtain ⟨ζ', hζ'⟩ := hex' p' hp'
    refine ⟨(hadd _ _ _ _ hζ hζ').1, ?_⟩
    have hn : ‖ζ‖ = 1 := norm_eq_one hζ.2.1
    have h0 : ζ ≠ 0 := by rintro rfl; simp at hn
    have hinv : ‖ζ⁻¹ - 1‖ < 1 := by
      have : ζ⁻¹ - 1 = -(ζ⁻¹ * (ζ - 1)) := by field_simp; ring
      rw [this, norm_neg, norm_mul, norm_inv, hn, inv_one, one_mul]; exact hζ.2.1
    obtain ⟨r, hr⟩ := hex _ hinv
    have h3 := hadd _ _ _ _ hr hζ
    rw [inv_mul_cancel₀ h0, one_iff, ← hL] at h3
    exact ((hlat _ r (-p) hr).2 (by rwa [sub_neg_eq_add])).1
  · rintro p ⟨s, -, hsq, hsp⟩ hp
    obtain ⟨ζ, hζ⟩ := hex' p hp
    have := eq_one_of_pow hζ.2.1 hsq (htors _ _ _ hζ hsp)
    subst this
    exact (one_iff _).1 hζ
  · rintro p α s hα hα0 ⟨t, ht, htq, hts⟩ hin hp
    obtain ⟨-, ⟨N, hN⟩, -⟩ := halg α hα
    have hN0 : N ≠ 0 := by
      rintro rfl
      have : α * conj α = 0 := by simpa using hN.symm
      rcases mul_eq_zero.1 this with h | h
      · exact hα0 h
      · exact hα0 (by simpa using h)
    have h2t : InOK d (((2 * t : ℕ) : ℂ) * (s - 1 / 2)) :=
      inOK_of_eq (iadd (imul (inOK_int d 2) hts) (inOK_int d (-t))) (by push_cast; ring)
    have hNp : InOK d (((2 * t * N : ℕ) : ℂ) * p) := by
      refine inOK_of_eq (imul (iconj hα) (iadd (imul (inOK_int d (2 * t)) hin)
        (imul (inOK_int d (-1)) h2t))) ?_
      push_cast; rw [hN]; ring
    obtain ⟨n, ζ, -, -, hk⟩ := h2 p _ (by positivity) hNp hp
    have hβ : ∀ β, InOK d β → ‖M.ι β‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (β * (s - 1 / 2)) := by
      intro β hβ hn
      refine inOK_of_eq (iadd (imul hβ hin) (imul (inOK_int d (-1)) (imul hα (hk β hβ hn)))) ?_
      push_cast; ring
    have hq2 : q ≠ 2 := by
      intro h
      obtain ⟨β, hβ1, hβ2, hβ3⟩ := hhalf n
      apply hβ3
      have hodd : Odd t := by
        rw [h] at htq; exact Nat.coprime_two_right.1 htq
      obtain ⟨k, hk'⟩ := hodd
      have hk2 : (t : ℂ) = 2 * k + 1 := by exact_mod_cast hk'
      refine inOK_of_eq (iadd (iadd (imul hβ1 hts) (imul (inOK_int d (-t)) (hβ β hβ1 hβ2)))
        (imul (inOK_int d (-k)) hβ1)) ?_
      push_cast; rw [hk2]; ring
    refine ⟨hq2, ?_⟩
    have hc : Nat.Coprime (2 * t) (q ^ n) := by
      refine Nat.Coprime.pow_right n (Nat.Coprime.mul_left ?_ htq)
      exact (Nat.coprime_primes Nat.prime_two hq.out).2 hq2.symm
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
    have hab' : (a : ℂ) * ((2 * t : ℕ) : ℂ) + b * (q : ℂ) ^ n = 1 := by exact_mod_cast hab
    have h3 := hβ ((q : ℂ) ^ n) (inOK_of_eq (inOK_int d (q ^ n)) (by push_cast; rfl))
      (by rw [map_pow, map_natCast, norm_q_pow])
    refine inOK_of_eq (iadd (imul (inOK_int d a) h2t) (imul (inOK_int d b) h3)) ?_
    linear_combination (s - 1 / 2) * hab'

end GlobalTheory.MomOne
