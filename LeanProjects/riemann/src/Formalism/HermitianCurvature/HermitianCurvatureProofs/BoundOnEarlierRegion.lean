import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLSubOneCcle
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffFormOf

noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bound_on_earlier_region : OnOldBound := by
  intro k ρ Wp Wq _ _ _ _ Bs w m
  obtain ⟨K, hK, hM⟩ := mDiff_ccle Bs w m
  refine ⟨K, hK, fun σ hσ ys => ?_⟩
  induction ys with
  | nil => intro A x c hx e; exact hM σ hσ A x c hx e
  | cons y ys ih =>
    intro A x c hx e
    exact ih A (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) c (fun e' => hx _)
      (fun a => e a.succ)

end Formalism.FourierDecayAlt.P.StandardPairingDecay
