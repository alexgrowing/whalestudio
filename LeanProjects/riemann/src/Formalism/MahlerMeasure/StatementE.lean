import Formalism.MahlerMeasure.StatementD

namespace Formalism.GM

def SmithBall : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K),
    (∀ i j, ‖M i j‖ ≤ 1) →
    ∃ (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
      (∀ i j, ‖U i j‖ ≤ 1) ∧ (∀ i j, ‖V i j‖ ≤ 1) ∧ ‖U.det‖ = 1 ∧ ‖V.det‖ = 1 ∧
      M = U * Matrix.diagonal d * V

end Formalism.GM
