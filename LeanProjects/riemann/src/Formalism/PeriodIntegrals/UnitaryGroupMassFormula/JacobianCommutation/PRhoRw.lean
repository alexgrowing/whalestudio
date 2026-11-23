import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.CutDefs
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.JCC

section twist

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

def twistL (A : Wp →L[ℂ] Wp) (B : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  (((ContinuousLinearMap.compL ℂ Wq Wp Wp) A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B)).restrictScalars ℝ

end twist

variable {k r : ℕ}

theorem uwset_inv {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  obtain ⟨h1, h2, h3⟩ := hh
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh h1
  have key : ∀ v, Matrix.mulVec h v = v → Matrix.mulVec h⁻¹ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h1, fun a => ⟨key _ (h2 a).1, key _ (h2 a).2⟩, key _ h3⟩

section rho

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

end rho

end PI.UnitaryGroupMassFormula.JCC
