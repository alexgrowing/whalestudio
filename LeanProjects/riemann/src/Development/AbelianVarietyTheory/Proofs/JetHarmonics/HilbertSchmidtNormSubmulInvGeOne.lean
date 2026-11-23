import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix

namespace GlobalTheory.BesselNorm

theorem hilbertSchmidt_normInv : Formalism.FourierDecayAlt.ThreeDimData.NormInv := fun _ _ =>
  ⟨fun x y => PI.PolynomialProperness.GN.gN_mul_le x y,
    fun _ hx => ⟨PI.PolynomialProperness.GN.gN_inv hx, PI.PolynomialProperness.GN.gN_ge_one hx⟩⟩

end GlobalTheory.BesselNorm
