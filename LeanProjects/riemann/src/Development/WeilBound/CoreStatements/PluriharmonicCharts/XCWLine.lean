import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsPenFrame
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorElementaryColumnOp
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsPositivePeriodLine
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_w_line : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ G : GenFibre (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), ∃ T : Set (MRingOver G.Φ (fibreIdx (fun o : Option K => ι (o.getD k₀)) (some : K → Option K))), (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hab hk hca hcb
  choose c hc using PositivityTheory.Xgp.W.blocks_of_model M
  obtain ⟨Fr⟩ := PositivityTheory.Xgp.W.exists_penFrame M hb hab hk hca hcb (PositivityTheory.Xgp.W.isPt_self fun k => ⟨c k, hc k⟩) c hc
  rw [PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb]
  exact fun G => PositivityTheory.Xgp.W.line_pen Fr G
