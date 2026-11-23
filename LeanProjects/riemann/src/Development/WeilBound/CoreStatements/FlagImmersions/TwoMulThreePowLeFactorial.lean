import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PrimeWeightEqZeroOfLt
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestInnerTsumBound
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LieTermFlagBoundStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormulaStatement
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

open GroundTheory.Heights₂.Heights.RestTerms (RestInnerTsumBound.proof)
open GroundTheory.Heights₂.Heights.RestTerms.Elem (primeWeight primeWeight_nonneg prime_partial_le)

theorem two_mul_three_pow_le_factorial (n : ℕ) : (2 : ℝ) * 3 ^ n ≤ ((n + 2).factorial : ℝ) := by
  induction n with
  | zero => norm_num [Nat.factorial]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ]
    push_cast
    have h3 : (0 : ℝ) ≤ 2 * 3 ^ n := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [pow_succ]
    nlinarith

theorem factorial_half_power_sum_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + 1), (if 2 ≤ k then (1 / 2 : ℝ) ^ (k - 1) / (k.factorial : ℝ) else 0) ≤
      0.3 - 0.3 * (1 / 6 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), if_pos (by omega)]
    have h1 : (1 / 2 : ℝ) ^ (n + 1 + 1 - 1) / ((n + 1 + 1).factorial : ℝ) ≤ 1 / 4 * (1 / 6) ^ n := by
      have h := two_mul_three_pow_le_factorial n
      have h3 : (0 : ℝ) < 2 * 3 ^ n := by positivity
      calc (1 / 2 : ℝ) ^ (n + 1 + 1 - 1) / ((n + 1 + 1).factorial : ℝ)
          ≤ (1 / 2 : ℝ) ^ (n + 1) / (2 * 3 ^ n) :=
            div_le_div_of_nonneg_left (by positivity) h3 h
        _ = 1 / 4 * (1 / 6) ^ n := by
            rw [show (1 / 6 : ℝ) = 1 / 2 * (1 / 3) by norm_num, mul_pow, pow_succ, one_div_pow (3 : ℝ)]
            field_simp
            norm_num
    rw [pow_succ (1 / 6 : ℝ)]
    linarith

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem rest_term_prime_bound (j p : ℕ) (fr : ℕ → Ψ ⊕ Ψ) (k : ℕ) (Q : RP Ψ N) (M : ℝ) (hp : 2 ≤ p) (hk : 2 ≤ k)
    (hM : ∀ σ, |k * degFl (pLie j (k - 1) σ * Q)| ≤ M) :
    |restTerm j p fr k Q| ≤ Real.log p * (M * (2 * ((p : ℝ) ^ k)⁻¹)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h := (RestInnerTsumBound.proof p k (fun n => k * degFl (pLie j (k - 1) (fr n) * Q)) M hp' (by omega)
    (fun n => hM _)).2
  unfold restTerm
  rw [if_pos hk, mul_assoc, ← tsum_mul_left, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg p)
  refine le_of_eq_of_le ?_ h
  congr 2
  funext n
  rw [mul_comm (n + 1) k, pow_mul, inv_pow]
  ring

theorem rest_sum_primes_bound (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N)
    (M b : ℝ) (hb : 0 < b) (hB : b < B + 1) (hk : 2 ≤ k)
    (hM : ∀ σ, |k * degFl (pLie j (k - 1) σ * Q)| ≤ M) :
    |restSum j bad frob B τ k Q| ≤ M * (5.56 / b ^ (k - 1)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Sum.inl τ))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  set K : ℝ := M * 2 / b ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  set w : ℕ → ℝ := fun i => K * (primeWeight b i / (i : ℝ) ^ 2) with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => mul_nonneg hK0 (div_nonneg (primeWeight_nonneg b i) (by positivity))
  have hpart : ∀ n, ∑ i ∈ Finset.range n, w i ≤ K * (2 * Real.log 4 / b) := fun n => by
    simp only [hw]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (prime_partial_le b hb n) hK0
  have hws : Summable w := summable_of_sum_range_le hw0 hpart
  have hle : ∀ p : ℕ, ‖(if p.Prime ∧ B < p ∧ p ∉ bad then restTerm j p (frob p τ) (m + 2) Q else 0)‖ ≤ w p := by
    intro p
    split_ifs with h
    · have hbp : b < p := by
        have : (B : ℝ) + 1 ≤ p := by exact_mod_cast h.2.1
        linarith
      have hpw : primeWeight b p = Real.log p := by simp [primeWeight, h.1, hbp]
      have hp0 : (0 : ℝ) < p := hb.trans hbp
      have hl := Real.log_natCast_nonneg p
      rw [Real.norm_eq_abs]
      refine (rest_term_prime_bound j p _ _ Q M h.1.two_le hk hM).trans ?_
      simp only [hw, hK, hpw]
      have h1 : b ^ m ≤ (p : ℝ) ^ m := pow_le_pow_left₀ hb.le hbp.le m
      calc Real.log p * (M * (2 * ((p : ℝ) ^ (m + 2))⁻¹)) = M * 2 / (p : ℝ) ^ m * (Real.log p / (p : ℝ) ^ 2) := by
            field_simp
            ring
        _ ≤ M * 2 / b ^ m * (Real.log p / (p : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1
    · simpa using hw0 p
  have h2 := tsum_of_norm_bounded hws.hasSum hle
  rw [Real.norm_eq_abs] at h2
  refine h2.trans ((Real.tsum_le_of_sum_range_le hw0 hpart).trans ?_)
  have h4 : 2 * Real.log 4 ≤ 2.78 := (GroundTheory.Heights₂.Heights.RestTerms.RestConstants.intersectionNumber_baseChange).1
  calc K * (2 * Real.log 4 / b) ≤ K * (2.78 / b) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h4 hb.le) hK0
    _ = M * (5.56 / b ^ (m + 2 - 1)) := by
        rw [hK, show m + 2 - 1 = m + 1 by omega, pow_succ]
        field_simp
        ring

theorem rest_sum_total_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (u : Wt Ψ N) (g : ℝ) (B : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → bigB0 u g < B + 1 → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤ 2 * (((dimFl Ψ N : ℝ) + 1) * flagDeg u) * ((min j (N - j) : ℕ) * spread u) := by
  intro Ψ _ _ N j bad frob u g B Q hj hjN hW hB hQ
  have hg : 0 < g := hW.1
  have hD : 0 < flagDeg u := (GlobalTheory.T.flag_degree_weight_formula Ψ N u).2.1 hW.2.1
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hH : 0 ≤ ‖u‖ / g := by positivity
  set E : ℝ := ((dimFl Ψ N : ℝ) + 1) * flagDeg u with hE
  have hE0 : 0 ≤ E := by positivity
  set j' : ℝ := ((min j (N - j) : ℕ) : ℝ) with hj'
  have hj0 : 0 ≤ j' := Nat.cast_nonneg _
  have key : ∀ τ, |∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤
      2 * E * (j' * ((⨆ i, u τ i) - ⨅ i, u τ i)) := by
    intro τ
    have hf : (1 : ℝ) ≤ Fintype.card Ψ := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨τ⟩ : 0 < Fintype.card Ψ)
    set U : ℝ := (⨆ i, u τ i) - ⨅ i, u τ i with hU
    have hU0 : 0 ≤ U := by
      have a : Fin N := ⟨0, by omega⟩
      have h1 := le_ciSup (Set.finite_range (u τ)).bddAbove a
      have h2 := ciInf_le (Set.finite_range (u τ)).bddBelow a
      linarith
    set A : ℝ := N * (1 + 2 * (‖u‖ / g)) with hA
    have hA0 : 0 ≤ A := by positivity
    have hb : 0 < bigB0 u g := by unfold bigB0; positivity
    have hAb : 2 * A / bigB0 u g ≤ 1 / 2 := by
      rw [div_le_iff₀ hb, hA]
      unfold bigB0
      set H := ‖u‖ / g
      have h1 : 2 * (N : ℝ) ≤ Fintype.card Ψ * (N : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hterm : ∀ k ∈ Finset.Icc 1 N, |restSum j bad frob B τ k (Q τ k)| ≤
        5.56 * (E * (j' * U)) * (if 2 ≤ k then (1 / 2 : ℝ) ^ (k - 1) / (k.factorial : ℝ) else 0) := by
      intro k hk
      split_ifs with h2
      · refine (rest_sum_primes_bound j bad frob B τ k (Q τ k) _ _ hb hB h2
          (fun σ => GlobalTheory.T.lie_term_flag_bound Ψ N j u g Q hj hjN hW hQ τ σ k h2 (Finset.mem_Icc.mp hk).2)).trans ?_
        have h3 : (2 * A / bigB0 u g) ^ (k - 1) ≤ (1 / 2 : ℝ) ^ (k - 1) :=
          pow_le_pow_left₀ (by positivity) hAb _
        calc E * (j' * (2 ^ (k - 1) / (k.factorial : ℝ)) * U * A ^ (k - 1)) * (5.56 / bigB0 u g ^ (k - 1))
            = 5.56 * (E * (j' * U)) * ((2 * A / bigB0 u g) ^ (k - 1) / (k.factorial : ℝ)) := by
              rw [div_pow, mul_pow 2 A]; ring
          _ ≤ _ := by gcongr
      · simp [restSum, restTerm, h2]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hs := factorial_half_power_sum_le n
    have h6 : (0 : ℝ) ≤ (1 / 6 : ℝ) ^ n := by positivity
    have hX : 0 ≤ E * (j' * U) := by positivity
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum]
    nlinarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun τ _ => key τ).trans (le_of_eq ?_))
  rw [spread, Finset.mul_sum, Finset.mul_sum]

end RootFieldNumerics
