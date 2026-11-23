import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselDerivatives.LiftAOneZero

open scoped ContDiff Topology
open Filter

noncomputable section

namespace PI.BesselDerivW

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

def r1 (a : E →L[ℝ] E) (G : E → V) (g : E) : V := fderiv ℝ G g (a g)

def r1W : List (E →L[ℝ] E) → (E → V) → E → V
  | [], G => G
  | a :: w, G => r1 a (r1W w G)

def r2W : List (E →L[ℝ] E) → (ℝ × E → V) → ℝ × E → V
  | [], Φ => Φ
  | a :: w, Φ => rX a (r2W w Φ)

end PI.BesselDerivW
