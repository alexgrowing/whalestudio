import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuLe
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuQDUnit
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.SumFactorizationMulLogLe
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.WDvdQS
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.SplitNotDvd

open NumberField Formalism.BasicNotions KStar.Tree

namespace UpperTheory.Mu

theorem tr_odd (R : Ranks) : Odd (R.t * R.r) := by
  refine Nat.odd_mul.2 ⟨R.t_odd, ?_⟩
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have hm := R.two_le_m
  unfold Ranks.r
  exact ⟨a + b - 1, by omega⟩

variable {R : Ranks} (H : Host R)

theorem half_not_dvd {l : ℕ} (h : l = H.q ∨ l = H.d) : ¬ (l - 1) / 2 ∣ R.t * R.r := by
  have hpos : 0 < R.t * R.r := (tr_odd R).pos
  obtain ⟨hq, hd⟩ := H.qd_big
  have e : 4 * R.t * R.r = 4 * (R.t * R.r) := by ring
  rw [e] at hq hd
  apply Nat.not_dvd_of_pos_of_lt hpos
  generalize R.t * R.r = N at *
  rcases h with rfl | rfl <;> omega

theorem w_dvd_QS : H.w ∣ H.QS := (wDvdQS _ H.toHostRaw H.q_ne_three).1

variable (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

theorem nu_eq_zero_of_qd (l : ℕ) [Fact l.Prime] (h : l = H.q ∨ l = H.d) : nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 :=
  nuQD _ H.toHostRaw l Ω _ h (half_not_dvd H h)

theorem nu_eq_zero_of_not_dvd (l : ℕ) [Fact l.Prime] (h : ¬ l ∣ H.QS) : nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 := by
  by_cases hqd : l = H.q ∨ l = H.d
  · exact nu_eq_zero_of_qd H Ω l hqd
  · push_neg at hqd
    have hle := nuLe _ H.toHostRaw l Ω (R.t * R.r) (tr_odd R) hqd.1 hqd.2
    rw [if_neg h, Nat.factorization_eq_zero_of_not_dvd h] at hle
    omega

theorem nu_eq_zero_of_split (l : ℕ) [hl : Fact l.Prime]
    (h : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E) | ((l : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E) :
    nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 :=
  nu_eq_zero_of_not_dvd H Ω l (splitNotDvd _ H.toHostAx H.QS_exact l hl.out h)

theorem sum_nu_le (ν : ℕ → ℝ) (hν : ∀ (l : ℕ) [Fact l.Prime], ν l = (nuOf l (cyc l H.E Ω) (R.t * R.r) : ℝ))
    (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, ν l * Real.log l ≤ Real.log (H.QS : ℝ) + Real.log ((R.t * R.r : ℕ) : ℝ) := by
  classical
  let μ : ℕ → ℕ := fun l => if h : l.Prime then (haveI := Fact.mk h; nuOf l (cyc l H.E Ω) (R.t * R.r)) else 0
  have hμ : ∀ (l : ℕ) [Fact l.Prime], μ l = nuOf l (cyc l H.E Ω) (R.t * R.r) := fun l hl => dif_pos hl.out
  refine le_of_eq_of_le (Finset.sum_congr rfl fun l hl => ?_)
    (nuSum _ H.toHostRaw Ω _ (tr_odd R) (half_not_dvd H (Or.inl rfl)) (half_not_dvd H (Or.inr rfl)) μ hμ S hS)
  haveI := Fact.mk (hS l hl)
  rw [hν l, hμ l]

theorem budget_le : Real.log (H.QS : ℝ) + Real.log ((R.t * R.r : ℕ) : ℝ) ≤
    2 * Real.log R.n + Real.log R.t + Real.log R.r := by
  have h1 : Real.log (H.QS : ℝ) ≤ 2 * Real.log R.n := by
    have : ((H.QS : ℕ) : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast H.QS_le
    have h0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
    simpa using Real.log_le_log h0 this
  have h2 := (tr_odd R).pos
  have ht : (R.t : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right h2).ne'
  have hr : (R.r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left h2).ne'
  rw [Nat.cast_mul, Real.log_mul ht hr]
  linarith

end UpperTheory.Mu
