import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.RhoFinal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.LatLink
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LieComplementChartContDiffAt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ExistsLim
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

set_option maxHeartbeats 1000000

open Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem levSys_ex' [FiniteDimensional ℚ_[l] K] : ∃ S : LevSys (per l K), S.Good ∧ ∀ m, (S.L m).CrisOK := CrystallineSemistableComparison.HT.levSys_ex

theorem rhoSys_ex' [FiniteDimensional ℚ_[l] K] (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK) :
    Nonempty (RhoSys S Model.Sm (dat Amp) fun {M} a c => IsFirstChernDeRham M.q (lineK a.1) c) := Mo.rhoSys_ex S hS hC

theorem crystalline_deRham_firstChern_exists [FiniteDimensional ℚ_[l] K] : ∃ L : KapL (l := l) (K := K) Amp, LieComplementChartContDiffAt L := by
  obtain ⟨S, hS, hC⟩ := levSys_ex' (l := l) (K := K)
  obtain ⟨P⟩ := rhoSys_ex' S hS hC
  obtain ⟨A⟩ := kap_abs (facts l K) (fun c => ⟨_, rfl⟩) hS P
  exact ⟨⟨A.κ, A.lin, A.lin', A.act, A.nat, A.fil, A.cup, A.one⟩, A.c1⟩

end CrystallineSemistableComparison.Pb
