import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveModelExistsAllPrimesAllPoints
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveModel_exists_all_primes_allPoints : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), GenValInjSt h j hG → CompSplitSt h j hG → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → CurveInstSt h j hj := by
  first | exact @GlobalTheory.CurveRecord.curveInst | exact GlobalTheory.CurveRecord.curveInst | (intros; apply GlobalTheory.CurveRecord.curveInst <;> assumption)
