import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvEig
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvAssoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ExistsCompactTail
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.OpLeHalf

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.kills_of_idem :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (e : G → ℂ),
      IsRay N a H → Continuous e → Integrable e μ → (∀ x, conv μ e e x = e x) → Kills μ N a e := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H e hR hc hi hid
  have step1 : ∀ s, OpLe μ N a e s (1 / 2) → OpLe μ N a e s 0 := by
    intro s hs
    have hk : ∀ k : ℕ, OpLe μ N a e s ((1 / 2) ^ (k + 1)) := by
      intro k
      induction k with
      | zero => simpa using hs
      | succ k ih =>
        intro C h hh x
        have h1 := conv_isEig G μ N a e h s C hi hh
        have h2 : IsEig N a s (1 / 2 * C) (conv μ e h) := ⟨h1.1, hs C h hh, h1.2.2.1, h1.2.2.2⟩
        have h3 := ih _ _ h2 x
        rw [← conv_assoc G μ e e h C hc hi hc hi hh.1 hh.2.1 hid x] at h3
        calc _ ≤ _ := h3
          _ = _ := by ring
    intro C h hh x
    have ht : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ (k + 1)) * C) atTop (𝓝 (0 * C)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)).mul_const C
    exact ge_of_tendsto' ht (fun k => hk k C h hh x)
  obtain ⟨δ, hδ, hnear⟩ := opLe_near G μ N a H e hR hi (1 / 2) (by norm_num)
  have step2 : ∀ s s', |s - s'| < δ → OpLe μ N a e s 0 → OpLe μ N a e s' 0 := by
    intro s s' hss hs
    have := hnear s s' 0 hss hs
    rw [zero_add] at this
    exact step1 s' this
  obtain ⟨s₀, hs₀⟩ := opLe_half G μ N a H e hR hi
  have h0 := step1 s₀ hs₀
  have step3 : ∀ n : ℕ, ∀ s, |s - s₀| ≤ n * (δ / 2) → OpLe μ N a e s 0 := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have : s = s₀ := by
        have : |s - s₀| ≤ 0 := by simpa using hs
        linarith [abs_nonpos_iff.mp this]
      rw [this]; exact h0
    | succ n ih =>
      intro s hs
      have hn : (0 : ℝ) ≤ n * (δ / 2) := by positivity
      push_cast at hs
      rw [abs_le] at hs
      by_cases h1 : |s - s₀| ≤ n * (δ / 2)
      · exact ih s h1
      · rcases le_total s s₀ with h2 | h2
        · refine step2 (s₀ - n * (δ / 2)) s ?_ (ih _ ?_)
          · rw [abs_of_nonpos (by linarith), not_le] at h1
            rw [abs_lt]; constructor <;> nlinarith
          · rw [abs_le]; constructor <;> linarith
        · refine step2 (s₀ + n * (δ / 2)) s ?_ (ih _ ?_)
          · rw [abs_of_nonneg (by linarith), not_le] at h1
            rw [abs_lt]; constructor <;> nlinarith
          · rw [abs_le]; constructor <;> linarith
  intro s C h hh x
  obtain ⟨n, hn⟩ := exists_nat_ge (|s - s₀| / (δ / 2))
  rw [div_le_iff₀ (by positivity)] at hn
  have := step3 n s hn C h hh x
  rw [zero_mul] at this
  exact norm_le_zero_iff.mp this
