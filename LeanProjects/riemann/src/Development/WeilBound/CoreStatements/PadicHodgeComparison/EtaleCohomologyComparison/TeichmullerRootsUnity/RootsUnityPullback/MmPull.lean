import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.TUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.crystallineComparison.PinP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def mm (r : Res l K) (M : Model l K) (n : ℕ) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N) : MuMor r M n :=
  (Pb.bWMor r M n).comp (σ'' := r.w) (Pb.Mid.muMor r M n hT)

theorem mm_pull (r : Res l K) (M : Model l K) (n j : ℕ) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N)
    (y : (Pb.HSW r M j).M n) : (mm r M n hT).pull j y = Pb.Mid.mu r M n j hT (Pb.bW r M n j y) :=
  (CrystallineSemistableComparison.P.pull_comp (Pb.bWMor r M n) (Pb.Mid.muMor r M n hT) j y).1

end CrystallineSemistableComparison.crystallineComparison.PinP
