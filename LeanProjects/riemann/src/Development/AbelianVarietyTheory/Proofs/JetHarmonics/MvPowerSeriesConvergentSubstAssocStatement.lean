import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstAssoc
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_assoc : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ρ σ τ : Type) [Fintype ρ] [Fintype σ] (s : ρ → MvPowerSeries σ K) (t : σ → MvPowerSeries τ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → (∀ i, Small (t i)) → Bdd S → (∀ j, Small (csub t (s j))) ∧ csub t (csub s S) = csub (fun j => csub t (s j)) S := by
  first | exact @GlobalTheory.ConvSer.csub_assoc | exact GlobalTheory.ConvSer.csub_assoc | (intros; apply GlobalTheory.ConvSer.csub_assoc <;> assumption)
