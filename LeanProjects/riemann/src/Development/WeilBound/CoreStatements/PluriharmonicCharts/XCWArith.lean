import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsPenFrame
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorElementaryColumnOp

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_w_arith : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M d τ a b k₀ ca cb hb hab hk hca hcb har
  haveI : CharZero Φ := PositivityTheory.Xgp.W.charZero_of_model M
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := PositivityTheory.Xgp.W.blocks_of_model M
  choose c hc using hne
  have hpt : PositivityTheory.Xgp.W.IsPt y y := PositivityTheory.Xgp.W.isPt_self (fun k => ⟨c k, hc k⟩)
  obtain ⟨Fr⟩ := PositivityTheory.Xgp.W.exists_penFrame M hb hab hk hca hcb hpt c hc
  have hA := PositivityTheory.Xgp.W.arith_pen hc Fr (d := d + 1) har
  rw [PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb, PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb,
    PositivityTheory.Xgp.W.ideal_pen_zero]
  refine ⟨hA.1, hA.2, PositivityTheory.Xgp.W.pen_le_zero _ _ _ _, PositivityTheory.Xgp.W.image_pen _ _ _ _ _, ?_⟩
  intro v₁ h1 h2
  rw [← PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb]
  exact PositivityTheory.Xgp.W.image_snd M hb hab hk hca hcb v₁ h1 h2
