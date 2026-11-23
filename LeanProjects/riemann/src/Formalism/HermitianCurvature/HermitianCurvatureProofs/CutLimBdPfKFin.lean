import Formalism.PeriodIntegrals.UpqRep
import Formalism.HermitianCurvature.StatementB

namespace Formalism.FourierDecayAlt.P.CutBP

noncomputable section

def KFinDSCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ : B.Mat k r → (H →L[ℂ] H)) (Pm : H →L[ℂ] Wp) (Qm : Wq →L[ℂ] H),
    PI.UpqRep.IsHCParam lam ∧ PI.UpqRep.IsDSHpk k r ε lam σ ∧
    (∀ w, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (Qm w)) ∧
    (∀ x, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (ContinuousLinearMap.adjoint Pm x)) ∧
    ∀ g ∈ B.GV k r, F g = Pm.comp ((σ g).comp Qm)

end

end Formalism.FourierDecayAlt.P.CutBP
