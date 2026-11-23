import Formalism.MahlerMeasure.StatementE

namespace Formalism.GM

namespace SmithNormalFormAlt

open Matrix

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def Dec {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) : Prop :=
  ∃ (U V : Matrix ι ι K) (d : ι → K),
      (∀ i j, ‖U i j‖ ≤ 1) ∧ (∀ i j, ‖V i j‖ ≤ 1) ∧ ‖U.det‖ = 1 ∧ ‖V.det‖ = 1 ∧
      M = U * Matrix.diagonal d * V

end SmithNormalFormAlt

end Formalism.GM
