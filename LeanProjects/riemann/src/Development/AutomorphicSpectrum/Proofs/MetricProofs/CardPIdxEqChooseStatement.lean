import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CardPIdxEqChoose
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_pIdx_eq_choose : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (keep : Ψ × Fin N → Prop), j ≤ N → (∀ p, keep p) → Nat.card (PIdx j keep) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept.card_pIdx_of_all | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept.card_pIdx_of_all | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept.card_pIdx_of_all <;> assumption)
