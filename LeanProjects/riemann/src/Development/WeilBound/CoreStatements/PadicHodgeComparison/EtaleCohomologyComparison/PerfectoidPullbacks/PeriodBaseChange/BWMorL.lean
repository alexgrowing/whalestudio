import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittToAcrisIsDPMorphismStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PhiTTmul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.MuMor
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def idA (r : Res l K) : AW r →+* Acris l := RingHom.id (Acris l)

def bWMorL (r : Res l K) (M : Model l K) (n : ℕ) :
    CH.Mor (Wc.OM l (B.schFn M.p) r.ρ n) (B.OM (Mid.Lm r M n) ((base l).cris n)) r.w :=
  B.omMor (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (Mid.wn r n) rfl (GlobalTheory.T.witt_to_acris_isDPMorphism r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    r.w (Mid.wn_mk r n)

def bWL (r : Res l K) (M : Model l K) (n j : ℕ) : (Wc.HS l (B.schFn M.p) r.ρ j).M n →ₛₗ[r.w] Mid.HM r M n j :=
  (bWMorL r M n).pull j

end CrystallineSemistableComparison.Pb
