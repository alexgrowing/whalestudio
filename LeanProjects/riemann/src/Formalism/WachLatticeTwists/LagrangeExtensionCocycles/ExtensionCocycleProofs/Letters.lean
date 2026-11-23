import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementLetters
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.TotallyRealRoots
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SecondDescentStatementHolds
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.ResidueQuotientHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem unit_lemma_prime_case_holds : StatWPrime := by
  intro ℓ _ hℓ A _ _ G n _ D _ _ _ _ Λ Mi hi s H hgen hM hh hgen2 hind hKH hs
  have hsH : ∀ i, s i ≤ H := fun i => (hs i).2 H (hKH i)
  have hℓ3 : 3 ≤ ℓ := by
    have h2 := (Fact.out : ℓ.Prime).two_le
    omega
  have part1 : ∀ i, s (i - 1) ≤ Mi i + hi i + cW ℓ H + 2 + (s i + (ℓ - 2)) / (ℓ - 1) := by
    intro i
    let S : PhiStep ℓ A D D :=
      { φA := Λ.φA, π := G.X, q := Λ.q, w := Λ.w, φπ := Λ.φπ, hq := Λ.hq, φ := Λ.φ i,
        φ_smul := Λ.φ_smul i, P := (Λ.pair (i - 1)).N, P' := (Λ.pair (i - 1)).N',
        R := (Λ.pair i).N, R' := (Λ.pair i).N' }
    have hc := second_descent_free_part_holds ℓ A D D S (Λ.pair (i - 1)).le hgen2 (by omega) (hind i)
    have he : ∀ a j : ℕ, ((s i : ℝ) - j) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H ≤ a →
        ∀ r ∈ S.R, ((ℓ : A) ^ a * S.π ^ j) • r ∈ S.R' := fun a j ha =>
      unconditional_first_statement ℓ hℓ A G D (Λ.pair i) (s i) H a j hgen (hsH i) (hs i).1 ha
    have key := second_descent_statement_holds ℓ hℓ A D D S (Mi i) (hi i) (s i) H (hM i) (hh i) hc (hs i).1 he
    exact (hs (i - 1)).2 (Mi i + hi i + cW ℓ H + 2 + (s i + (ℓ - 2)) / (ℓ - 1)) key
  have part2 : ∀ (i : ZMod n) (m : ℕ), (s i : ℝ) ≤
      (∑ a ∈ Finset.range m, (((Mi (i + ((a + 1 : ℕ) : ZMod n)) + hi (i + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)
        + cW ℓ H + 3) / ((ℓ : ℝ) - 1) ^ a) + (s (i + (m : ZMod n)) : ℝ) / ((ℓ : ℝ) - 1) ^ m := by
    intro i m
    have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
    refine residue_finite_holds n (ℓ : ℝ) (cW ℓ H : ℝ) (fun k => (s k : ℝ))
      (fun k => ((Mi k + hi k : ℕ) : ℝ)) hℓR ?_ i m
    intro k
    have h1 := part1 k
    have hℓ1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
    have hdiv : (((s k + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ) ≤ (s k : ℝ) / ((ℓ : ℝ) - 1) + 1 := by
      calc (((s k + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ)
          ≤ ((s k + (ℓ - 2) : ℕ) : ℝ) / ((ℓ - 1 : ℕ) : ℝ) := Nat.cast_div_le
        _ = ((s k : ℝ) + ((ℓ : ℝ) - 2)) / ((ℓ : ℝ) - 1) := by
          push_cast [Nat.cast_sub (show 2 ≤ ℓ by omega), Nat.cast_sub (show 1 ≤ ℓ by omega)]
          try ring
        _ ≤ (s k : ℝ) / ((ℓ : ℝ) - 1) + 1 := by
          rw [add_div]
          have : ((ℓ : ℝ) - 2) / ((ℓ : ℝ) - 1) ≤ 1 := by rw [div_le_one hℓ1]; linarith
          linarith
    have h1R : (s (k - 1) : ℝ) ≤
        ((Mi k + hi k + cW ℓ H + 2 + (s k + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_add] at h1R
    show (s (k - 1) : ℝ) ≤ ((Mi k + hi k : ℕ) : ℝ) + (cW ℓ H : ℝ) + 3 + (s k : ℝ) / ((ℓ : ℝ) - 1)
    rw [Nat.cast_add]
    norm_num at h1R ⊢
    linarith
  have part3 : ∀ i, (Λ.pair i).Kills ((ℓ : A) ^ cost ℓ 0 (s i)) ∧
      (cost ℓ 0 (s i) : ℝ) < (s i : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H := by
    intro i
    refine ⟨?_, ?_⟩
    · have h := cost_bound_kills_obstruction ℓ hℓ A G D (Λ.pair i) (s i) 0 hgen (Nat.zero_le _) (hs i).1
      simpa using h
    · have h := cost_bound ℓ hℓ 0 (s i) H (Nat.zero_le _) (hsH i)
      have hc : 1 + Real.logb ℓ ((H : ℝ) + 1) ≤ (cW ℓ H : ℝ) := Nat.le_ceil _
      simp only [Nat.cast_zero, sub_zero] at h
      linarith
  have part4 : ∀ (i : ZMod n) (j : ℕ) (Gw : ℝ), 0 ≤ Gw →
      (∀ k : ℕ, 1 ≤ k → k ≤ j → ((Mi (i + (k : ZMod n)) + hi (i + (k : ZMod n)) : ℕ) : ℝ) ≤ 2 * Gw) →
      (s i : ℝ) ≤ (2 * Gw + cW ℓ H + 3) * ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) +
        (H : ℝ) / ((ℓ : ℝ) - 1) ^ j := by
    intro i j Gw hGw hb
    have h2 := part2 i j
    have hℓ3R : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ3
    have hL : (1 : ℝ) < (ℓ : ℝ) - 1 := by linarith
    have hLpos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
    have hK0 : (0 : ℝ) ≤ 2 * Gw + cW ℓ H + 3 := by positivity
    set K : ℝ := 2 * Gw + cW ℓ H + 3 with hK
    have hsum : (∑ a ∈ Finset.range j, (((Mi (i + ((a + 1 : ℕ) : ZMod n)) +
        hi (i + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) + cW ℓ H + 3) / ((ℓ : ℝ) - 1) ^ a) ≤
        ∑ a ∈ Finset.range j, K / ((ℓ : ℝ) - 1) ^ a := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a < j := Finset.mem_range.mp ha
      have hak := hb (a + 1) (by omega) (by omega)
      apply div_le_div_of_nonneg_right _ (pow_pos hLpos a).le
      rw [hK]
      linarith
    have hgeom := geom_id K ((ℓ : ℝ) - 1) hL j
    have htail : 0 ≤ K * ((ℓ : ℝ) - 1) / (((ℓ : ℝ) - 1 - 1) * ((ℓ : ℝ) - 1) ^ j) := by
      apply div_nonneg (mul_nonneg hK0 hLpos.le)
      exact mul_nonneg (by linarith) (pow_pos hLpos j).le
    have hsH' : (s (i + (j : ZMod n)) : ℝ) / ((ℓ : ℝ) - 1) ^ j ≤ (H : ℝ) / ((ℓ : ℝ) - 1) ^ j :=
      div_le_div_of_nonneg_right (by exact_mod_cast hsH _) (pow_pos hLpos j).le
    have heq : K * ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1 - 1) = K * ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) := by
      rw [show (ℓ : ℝ) - 1 - 1 = (ℓ : ℝ) - 2 by ring]
    linarith
  exact ⟨part1, part2, part3, part4⟩

end Formalism.RepresentationBoundsCohomology.N2
