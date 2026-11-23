import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexPointKerEvalEqMaximal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexPoint_ker_eval_eq_maximal : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  first | (exact @GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (exact GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (intros; apply GlobalTheory.MaxPt.exists_cxPts_ker_eq  <;> assumption)
