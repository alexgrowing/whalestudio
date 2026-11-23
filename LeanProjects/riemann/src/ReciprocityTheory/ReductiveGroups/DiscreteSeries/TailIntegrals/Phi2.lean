import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.DetEqMulMinorOfColZero

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def phi2 (k r' : ℕ) (a : Fin (1 + r' + 1)) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  ιLev k 1 r' (Hpk k r') *ᵥ phiV k (1 + r') a

def Yx (k r' : ℕ) (x : HPar k r') (a : Fin (1 + r' + 1)) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  (heis0 k r' x)⁻¹ *ᵥ phi2 k r' a

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
