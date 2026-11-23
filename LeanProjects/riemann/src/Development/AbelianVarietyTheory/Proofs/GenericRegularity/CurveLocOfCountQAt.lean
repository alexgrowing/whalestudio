import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.IsAlgebraicOfTrdegEq
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdegStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

theorem curveLoc_of_countQAt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), CountQAtSt h j hj hG hT → ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w), ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧ phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a := by
  intro D T h j hj hG hT hQ ka wL wF G S g0 la hH Z r
  exact CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    (birAt_of h j hj hG hT G ((GlobalTheory.T.birational_of_formRatios_full_trdeg D T h j hj hG ka wL wF G).2 hH.2.1) Z)
    (hQ ka wL wF G S g0 la hH Z) r

end GlobalTheory
