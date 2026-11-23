import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.CrystallineFirstChernLevelCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.FinDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.RedInEx

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

def dOf (m n : ℕ) : RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) (S.L m).γ l n :=
  Classical.choose (redIn_ex (S.L m).γ (m + 1) (S.L m).lam ((hS.lev m).lat (m + 1) le_rfl).tf (hC m).1 (hC m).2 n)

theorem hcOf (m n : ℕ) (c : Acris l) :
    (dOf S hS hC m n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ ((S.L m).lam c) :=
  Classical.choose_spec (redIn_ex (S.L m).γ (m + 1) (S.L m).lam ((hS.lev m).lat (m + 1) le_rfl).tf (hC m).1 (hC m).2 n) c

abbrev chK (M : Model l K) (m s : ℕ) : Chain.{1} (per l K).A (S.L m).A (S.L m).B K :=
  chainOf (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)

def rhoK {M : Model l K} (a : (dat Amp).Ch M) (j m : ℕ) (x : ((dat Amp).H a).N j)
    (f : Module.Dual K (HdR M.q j) →+ (S.L m).B) : Prop :=
  M.Sm ∧ ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → (chK S hS hC M m s).Rho (show (M.HS false j).lim from x).1 f

variable [FiniteDimensional ℚ_[l] K]

end

end CrystallineSemistableComparison.Pb.Kap
