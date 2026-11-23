import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOLeft

open Matrix Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.Q.QnMinorLeftPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem left_quantum_minor_qMinorLeftH : QMinorLeftH := by
  intro E _ _ n t H f a b u h
  have hT : ∀ (c : ℂ) (i j : Fin n) (g : Matrix (Fin n) (Fin n) ℂ → E),
      Formalism.QuantumDeterminants.Top (EabH H) c i j (fun x => g (h * x)) = fun x => Formalism.QuantumDeterminants.Top (EabH H) c i j g (h * x) := by
    intro c i j g
    funext x
    simp only [Formalism.QuantumDeterminants.Top]
    rw [ioLeft_eabH_left]
  funext x
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [ioLeft_foldr_left h _ (fun T hTm g => ?_) f]
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hTm
  exact hT _ _ _ g

end Formalism.FourierDecayAlt.Q.QnMinorLeftPf
