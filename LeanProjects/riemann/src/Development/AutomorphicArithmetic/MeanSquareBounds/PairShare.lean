import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.Stage1Succ
import Development.AutomorphicArithmetic.MeanSquareBounds.CharOf

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem boxAll_mono {Q C C' τ Y X X' : ℝ} {f : ℕ → ℂ} {M : ℕ} (hC : C ≤ C') (hY : 1 ≤ Y) (hX : X' ≤ X)
    (h : BoxAll Q C τ Y X f M) : BoxAll Q C' τ Y X' f M := by
  intro N _ ψ hψ
  obtain ⟨h1, h2, h3⟩ := h N ψ hψ
  exact ⟨h1, le_trans h2 (mul_le_mul_of_nonneg_right hC (Real.log_nonneg hY)),
    fun y hy => h3 y ⟨hy.1, le_trans hy.2 hX⟩⟩

private theorem share_of_bad {P : Finset ℕ} {η : ℝ} (p : ℕ → Prop)
    (h : ∀ B ⊆ P, (∀ q ∈ B, ¬ p q) → (B.card : ℝ) ≤ η * P.card) :
    ∃ G ⊆ P, (1 - η) * P.card ≤ G.card ∧ ∀ q ∈ G, p q := by
  classical
  refine ⟨P.filter p, Finset.filter_subset _ _, ?_, fun q hq => (Finset.mem_filter.1 hq).2⟩
  have h1 := h (P.filter fun q => ¬ p q) (Finset.filter_subset _ _) (fun q hq => (Finset.mem_filter.1 hq).2)
  have h2 : ((P.filter p).card : ℝ) + ((P.filter fun q => ¬ p q).card : ℝ) = P.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := P) p
  linarith

theorem pair_share :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K η : ℝ) (N₀ : ℕ), 0 < ε → ε < 1 / 52 → 0 < τ → 1 ≤ K → 0 < η → 0 < N₀ → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ X z' : ℝ, X ≤ Y ^ K → Y ^ (ε / 5) * Real.log Y ^ 2 ≤ z' → z' ≤ K ^ 2 * (Y ^ (ε / 5) * Real.log Y ^ 2) →
      ∃ G₁ ⊆ primePairSetFirst (Y ^ (ε / 5)), 0 < (primePairSetFirst (Y ^ (ε / 5))).card ∧ (1 - η) * (primePairSetFirst (Y ^ (ε / 5))).card ≤ G₁.card ∧ ∀ q ∈ G₁,
        GoodQ N₀ C τ Y X (Y ^ (ε / 5)) q ∧ ∃ G₂ ⊆ primeSetTwoBounds (Y ^ (ε / 5)) z' q, 0 < (primeSetTwoBounds (Y ^ (ε / 5)) z' q).card ∧
          (1 - η) * (primeSetTwoBounds (Y ^ (ε / 5)) z' q).card ≤ G₂.card ∧ ∀ d ∈ G₂, GoodD N₀ C τ Y X (Y ^ (ε / 5)) z' q d := by
  obtain ⟨C1, hC1, h1⟩ := stage1
  obtain ⟨C2, hC2, h2⟩ := stage2
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun ε τ K η N₀ hε hε52 hτ hK hη hN₀ => ?_⟩
  obtain ⟨Y1, hY1⟩ := h1 ε τ K η N₀ hε hε52 hτ hK hη hN₀
  obtain ⟨Y2, hY2⟩ := h2 ε τ K η N₀ hε hε52 hτ hK hη hN₀
  refine ⟨max (max Y1 Y2) 1, fun Y hY X z' hX hz1 hz2 => ?_⟩
  have hYa : Y ≥ Y1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hYb : Y ≥ Y2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hYo : 1 ≤ Y := le_trans (le_max_right _ _) hY
  obtain ⟨hne1, hb1⟩ := hY1 Y hYa
  obtain ⟨G₁, hG₁s, hG₁c, hG₁⟩ :=
    share_of_bad (fun q => GoodQ N₀ C1 τ Y (Y ^ K) (Y ^ (ε / 5)) q) hb1
  have hS := hY2 Y hYb z' hz1 hz2
  refine ⟨G₁, hG₁s, hne1.card_pos, hG₁c, fun q hq => ⟨?_, ?_⟩⟩
  · intro ξ
    exact boxAll_mono (le_max_left _ _) hYo hX (hG₁ q hq ξ)
  · obtain ⟨hne2, hb2⟩ := hS q (hG₁s hq)
    obtain ⟨G₂, hG₂s, hG₂c, hG₂⟩ :=
      share_of_bad (fun d => GoodD N₀ C2 τ Y (Y ^ K) (Y ^ (ε / 5)) z' q d) hb2
    exact ⟨G₂, hG₂s, hne2.card_pos, hG₂c,
      fun d hd ξ a ha => boxAll_mono (le_max_right _ _) hYo hX (hG₂ d hd ξ a ha)⟩

end QH
