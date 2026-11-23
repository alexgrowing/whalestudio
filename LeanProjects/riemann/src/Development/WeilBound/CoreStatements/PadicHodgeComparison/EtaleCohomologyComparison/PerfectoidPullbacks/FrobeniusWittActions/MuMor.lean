import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb.Mid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) {N : ℕ}

abbrev HM (M : Model l K) (n j : ℕ) : Type 1 := CH.H (B.OM (Lm r M n) ((base l).cris n)) j

def muMor (M : Model l K) (n : ℕ) (hT : TeichmullerCongruence r N) :
    CH.Mor (B.OM (Lm r M n) ((base l).cris n)) (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n))
      (RingHom.id _) :=
  B.omMor (mIn r M n hT) (RingHom.id _) fun _ => rfl

def nuMor (M : Model l K) (n : ℕ) (hT : TeichmullerCongruence r N) :
    CH.Mor (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n)) (B.OM (Lm r M n) ((base l).cris n)) (phiA l N) :=
  B.omMor (mOut r M n hT) (phiA l N) (phiP_cris n N)

def mu (M : Model l K) (n j : ℕ) (hT : TeichmullerCongruence r N) :
    HM r M n j →ₗ[Acris l] CH.H (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n)) j :=
  (muMor r M n hT).pull j

def nu (M : Model l K) (n j : ℕ) (hT : TeichmullerCongruence r N) :
    CH.H (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n)) j →ₛₗ[phiA l N] HM r M n j :=
  (nuMor r M n hT).pull j

end CrystallineSemistableComparison.Pb.Mid
