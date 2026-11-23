import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings

namespace Formalism.FourierDecayAlt.P.PBI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

def HighestUnipotentIntegral : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)),
    KB.CptCoef p.T.base F → ζ ≠ 0 →
    D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν' →
    D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀ →
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)]

end

end Formalism.FourierDecayAlt.P.PBI
