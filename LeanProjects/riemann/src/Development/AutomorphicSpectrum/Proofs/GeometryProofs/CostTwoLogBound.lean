import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PrimeLogSum
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem log_div_pred_le_log_two {p : ℕ} (hp : p.Prime) : Real.log p / ((p : ℝ) - 1) ≤ Real.log 2 := by
  have h2 : 2 ≤ p := hp.two_le
  have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [div_le_iff₀ hpos]
  have hlt : p - 1 < 2 ^ (p - 1) := Nat.lt_two_pow_self
  have hle : p ≤ 2 ^ (p - 1) := by omega
  have hle' : (p : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by exact_mod_cast hle
  have h := Real.log_le_log (by linarith) hle'
  rw [Real.log_pow] at h
  have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hc] at h
  linarith

theorem sum_padicVal_log {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hsub : n.primeFactors ⊆ S) :
    ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p = Real.log n := by
  have h1 : ∑ p ∈ n.primeFactors, (padicValNat p n : ℝ) * Real.log p =
      ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p := by
    refine Finset.sum_subset hsub fun p hpS hp => ?_
    have hpp := hS p hpS
    have hnd : ¬ p ∣ n := fun hd => hp (Nat.mem_primeFactors.2 ⟨hpp, hd, hn⟩)
    simp [padicValNat.eq_zero_of_not_dvd hnd]
  rw [← h1]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity

theorem log_hostRd (E : Type) [Field E] [NumberField E] :
    Real.log (hostRd E) = Real.log ((discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) := by
  have hd : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  have he : |(discr E : ℝ)| = ((discr E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hostRd, Real.log_rpow hd, he]
  ring

theorem costTwo_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H)
    (B : ℝ) (hB : 128 ≤ B)
    (hbad : (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ ⌊B⌋₊) :
    0 ≤ costTwo l B ∧ costTwo l B ≤ 60 * (Real.log B + Real.log (hostRd E)) := by
  classical
  set N : ℕ := ⌊B⌋₊ with hN
  set P : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime with hP
  set Q : Finset ℕ := Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors with hQ
  set n : ℝ := (Module.finrank ℚ E : ℝ) with hn
  set d : ℕ := (discr E).natAbs with hd
  have hd0 : d ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hn0 : 0 < n := by
    rw [hn]; exact_mod_cast Module.finrank_pos
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  have hSp : ∀ p ∈ P ∪ Q, p.Prime := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · exact hPp p h
    · exact hQp p h
  have hcost : costTwo l B = ∑ p ∈ P ∪ Q, exTwo E p * Real.log p := by
    rw [costTwo, GlobalTheory.CompHt.htPrimes_eq, finsum_mem_coe_finset]
  have hterm : ∀ p ∈ P ∪ Q, exTwo E p * Real.log p =
      Real.log p / ((p : ℝ) - 1) + 40 / n * ((padicValNat p d : ℝ) * Real.log p)
        + (if p = 2 then Real.log 2 else 0) := by
    intro p _
    rw [exTwo, GlobalTheory.CovHt.htEx, ← hd, ← hn]
    by_cases h2 : p = 2
    · subst h2; simp only [if_true]; ring_nf
    · simp only [h2, if_false]; ring
  have ha0 : ∀ p : ℕ, p.Prime → 0 ≤ Real.log p / ((p : ℝ) - 1) := fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)

  have hA : ∑ p ∈ P ∪ Q, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 + (Real.log N + 1) := by
    have hN128 : 128 ≤ N := by
      rw [hN]; exact Nat.le_floor (by exact_mod_cast hB)
    have hNr : (128 : ℝ) ≤ N := by exact_mod_cast hN128
    have h3 : ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 := by
      have hPe : P = (Finset.Iic N).filter Nat.Prime := by
        ext p; simp [hP]
      rw [hPe]; exact ReciprocityTheory.ChartRestriction.G.H1.primeLogSum_nat N (by omega)
    have hL1 : 1 ≤ Real.log ((N : ℝ) + 1) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hL2 : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < ((N : ℝ) + 1) / N by positivity)
      rw [Real.log_div (by linarith) (by linarith)] at h
      have : ((N : ℝ) + 1) / N ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have h4 : ∑ p ∈ Q \ P, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 1 := by
      calc ∑ p ∈ Q \ P, Real.log p / ((p : ℝ) - 1) ≤ ∑ _p ∈ Q \ P, Real.log ((N : ℝ) + 1) / N := by
            refine Finset.sum_le_sum fun p hp => ?_
            obtain ⟨hq, hnp⟩ := Finset.mem_sdiff.1 hp
            have hp1 : N + 1 ≤ p := by
              by_contra hc
              exact hnp (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hQp p hq⟩)
            have hp2 : (N : ℝ) + 1 ≤ p := by exact_mod_cast hp1
            have h := Real.log_le_sub_one_of_pos (show 0 < (p : ℝ) / ((N : ℝ) + 1) from div_pos (by linarith) (by linarith))
            rw [Real.log_div (by linarith) (by linarith)] at h
            have h5 : (N : ℝ) * ((p : ℝ) / ((N : ℝ) + 1) - 1) ≤ p - (N + 1) := by
              have e : (p : ℝ) / ((N : ℝ) + 1) - 1 = (p - (N + 1)) / ((N : ℝ) + 1) := by field_simp
              rw [e, ← mul_div_assoc, div_le_iff₀ (by linarith)]
              nlinarith
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            nlinarith [mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ N by linarith),
              mul_le_mul_of_nonneg_left hL1 (show (0 : ℝ) ≤ p - (N + 1) by linarith)]
        _ = (Q \ P).card * (Real.log ((N : ℝ) + 1) / N) := by simp
        _ ≤ N * (Real.log ((N : ℝ) + 1) / N) := by
            have : (((Q \ P).card : ℕ) : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans hbad
            exact mul_le_mul_of_nonneg_right this (div_nonneg (by linarith) (by linarith))
        _ = Real.log ((N : ℝ) + 1) := by field_simp
        _ ≤ Real.log N + 1 := hL2
    rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
    linarith

  have hdsub : d.primeFactors ⊆ P ∪ Q := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdv := Nat.dvd_of_mem_primeFactors hp
    refine Finset.mem_union_right _ (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hpp, ?_, ?_⟩))
    · exact Dvd.dvd.mul_left hdv 2
    · exact mul_ne_zero two_ne_zero hd0
  have hC : ∑ p ∈ P ∪ Q, 40 / n * ((padicValNat p d : ℝ) * Real.log p) = 40 * Real.log (hostRd E) := by
    rw [← Finset.mul_sum, sum_padicVal_log hd0 hSp hdsub, log_hostRd]
    ring

  have hT0 : 0 ≤ ∑ p ∈ P ∪ Q, (if p = 2 then Real.log 2 else 0) :=
    Finset.sum_nonneg fun p _ => by
      split_ifs
      · exact Real.log_nonneg (by norm_num)
      · exact le_rfl
  have hT : ∑ p ∈ P ∪ Q, (if p = 2 then Real.log 2 else 0) ≤ Real.log 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact Real.log_nonneg (by norm_num)
  have hsum : costTwo l B = ∑ p ∈ P ∪ Q, Real.log p / ((p : ℝ) - 1) + 40 * Real.log (hostRd E)
      + ∑ p ∈ P ∪ Q, (if p = 2 then Real.log 2 else 0) := by
    rw [hcost, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib, hC]
  have hL : 0 ≤ Real.log (hostRd E) := by
    rw [log_hostRd]
    exact div_nonneg (Real.log_natCast_nonneg _) hn0.le
  have hA0 : 0 ≤ ∑ p ∈ P ∪ Q, Real.log p / ((p : ℝ) - 1) :=
    Finset.sum_nonneg fun p hp => ha0 p (hSp p hp)
  have hNB : Real.log N ≤ Real.log B := by
    have hN1 : 1 ≤ N := by
      rw [hN]; exact Nat.le_floor (by norm_num; linarith)
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hB7 : 7 * Real.log 2 ≤ Real.log B := by
    have h : Real.log ((2 : ℝ) ^ 7) ≤ Real.log B := Real.log_le_log (by norm_num) (by norm_num; linarith)
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  refine ⟨?_, ?_⟩
  · rw [hsum]; linarith
  · rw [hsum]; linarith

end GlobalTheory.CompanionTheory.Ar.Plug
