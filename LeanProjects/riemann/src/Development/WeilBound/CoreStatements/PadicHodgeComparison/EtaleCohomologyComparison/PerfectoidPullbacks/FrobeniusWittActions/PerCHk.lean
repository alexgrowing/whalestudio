import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.StmtPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.ResiduePadicIntegersToIntegers
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.NormLLtOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.MapFrobW
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.FrobAlg

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem perC_hk (r : Res l K) (w : WittVector l r.k) :
    r.perC.k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = r.perC.c (r.w w) := G3.perC_hk r w

theorem perC_hl (r : Res l K) : IsUnit (r.perC.c (l : (per l K).A)) := G3.perC_hl r

theorem perC_hφk (r : Res l K) (x : Wc.K₀ l r.k) : r.perC.φ (r.perC.k x) = r.perC.k (Wc.frob₀ l r.k x) := G3.perC_hφk r x

theorem w_fix (r : Res l K) [FiniteDimensional ℚ_[l] K] (g : K.fixingSubgroup) (w : WittVector l r.k) :
    (per l K).σA g (r.w w) = r.w w := G3.w_fix r g w

theorem perC_hσk (r : Res l K) [FiniteDimensional ℚ_[l] K] (g : K.fixingSubgroup) (x : Wc.K₀ l r.k) :
    r.perC.σ g (r.perC.k x) = r.perC.k x := G3.perC_hσk r g x

theorem w_phi (r : Res l K) (w : WittVector l r.k) : ACris.phi ℂ_[l] l (r.w w) = r.w (WittVector.frobenius w) := G3.w_phi r w

theorem teich (r : Res l K) [FiniteDimensional ℚ_[l] K] : ∃ N : ℕ, Mid.TeichmullerCongruence r N := G3.teich r

end CrystallineSemistableComparison.Pb
