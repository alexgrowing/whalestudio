import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.PairShare
import Development.AutomorphicArithmetic.MeanSquareBounds.RowsOfMem

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem pair_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K : ℝ) (N₀ : ℕ), 0 < ε → ε < 1 / 52 → 0 < τ → 1 ≤ K → 0 < N₀ → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ X z' : ℝ, X ≤ Y ^ K → Y ^ (ε / 5) * Real.log Y ^ 2 ≤ z' → z' ≤ K ^ 2 * (Y ^ (ε / 5) * Real.log Y ^ 2) →
      ∃ q d : ℕ, Rows (Y ^ (ε / 5)) z' q d ∧ N₀ < q ∧ GoodQ N₀ C τ Y X (Y ^ (ε / 5)) q ∧ GoodD N₀ C τ Y X (Y ^ (ε / 5)) z' q d := by
  obtain ⟨C, hC, H⟩ := pair_share
  refine ⟨C, hC, fun ε τ K N₀ hε hε' hτ hK hN => ?_⟩
  obtain ⟨Y₁, H1⟩ := H ε τ K (1 / 2) N₀ hε hε' hτ hK (by norm_num) hN
  have hev : ∀ᶠ Y : ℝ in Filter.atTop, (2 * N₀ : ℝ) ≤ Y ^ (ε / 5) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 5)).eventually_ge_atTop _
  obtain ⟨Y₂, H2⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max (max Y₁ Y₂) (Real.exp 2), fun Y hY X z' hX hz1 hz2 => ?_⟩
  have hY1 : Y₁ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hY2 : Y₂ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hY3 : Real.exp 2 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos 2) hY3
  have hlog : 2 ≤ Real.log Y := (Real.le_log_iff_exp_le hY0).2 hY3
  have hz : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hY0 _
  have hl2 : 2 ≤ Real.log Y ^ 2 := by nlinarith
  have hzz : 2 * Y ^ (ε / 5) ≤ z' := by nlinarith
  obtain ⟨G₁, hG₁, hp1, hc1, H3⟩ := H1 Y hY1 X z' hX hz1 hz2
  have hne1 : G₁.Nonempty := by
    rw [← Finset.card_pos]
    have h0 : (0 : ℝ) < (primePairSetFirst (Y ^ (ε / 5))).card := by exact_mod_cast hp1
    have h1 : (0 : ℝ) < G₁.card := by linarith
    exact_mod_cast h1
  obtain ⟨q, hq⟩ := hne1
  obtain ⟨hgq, G₂, hG₂, hp2, hc2, H4⟩ := H3 q hq
  have hne2 : G₂.Nonempty := by
    rw [← Finset.card_pos]
    have h0 : (0 : ℝ) < (primeSetTwoBounds (Y ^ (ε / 5)) z' q).card := by exact_mod_cast hp2
    have h1 : (0 : ℝ) < G₂.card := by linarith
    exact_mod_cast h1
  obtain ⟨d, hd⟩ := hne2
  have hR := rows_of_mem _ z' q d hz hzz (hG₁ hq) (hG₂ hd)
  refine ⟨q, d, hR, ?_, hgq, H4 d hd⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hR.q_prime.pos
  have h1 := hR.q_gt
  have h2 := Real.log_le_sub_one_of_pos hq0
  have h3 := H2 Y hY2
  have h4 : (N₀ : ℝ) < q := by linarith
  exact_mod_cast h4

end QH
