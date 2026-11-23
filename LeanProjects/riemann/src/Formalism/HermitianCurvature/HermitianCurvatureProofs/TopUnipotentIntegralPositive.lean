import Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVAppendSingletonEqVecVSliceAt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialHeadTypes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralRankZero

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

theorem top_unipotent_integral_positive (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r))
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) (hR : 1 ≤ P.r) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have h0 := p.hT 0 (Nat.zero_le _)
  have hr := p.hT P.r le_rfl
  exact vecV_append_singleton_eq_vecV_sliceAt P.k P.r (P.r - P.r) (Nat.sub_self _) (by omega) p.T.base (p.T.bs P.r)
    (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) (p.T.π_lev P.r le_rfl) (p.T.π'_lev P.r le_rfl)
    h0.2.2 h0.1 h0.2.1 hr.1 hr.2.1 hr.2.2 p.ν' p.m₀ ν'r m₀r hν hm p.hF
    (CompactCoefficientAppend.baseFrame_last p ν'r m₀r hν hm) h hh ζ hζ F hF hR _

theorem highestUnipotentIntegral : PBI.HighestUnipotentIntegral := by
  intro Wp Wq _ _ _ _ _ _ P p F h ζ hh ν'r m₀r hF hζ hν hm
  by_cases hR : P.r = 0
  · exact CompactCoefficientAppend.top_unipotent_integral_zero Wp Wq P p F h ζ hh ν'r m₀r hR hF hζ hν hm
  · exact top_unipotent_integral_positive Wp Wq P p F h ζ hh ν'r m₀r hF hζ hν hm (by omega)

end Formalism.FourierDecayAlt.P.PBM

namespace Formalism.FourierDecayAlt.P

theorem top_unipotent_integral : PBI.HighestUnipotentIntegral := PBM.highestUnipotentIntegral

end Formalism.FourierDecayAlt.P
