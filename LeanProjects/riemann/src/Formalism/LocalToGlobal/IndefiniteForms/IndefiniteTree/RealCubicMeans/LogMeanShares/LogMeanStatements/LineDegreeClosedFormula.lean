import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.NormVectorIdentities.Items

variable (K : Type) [Field K] [NumberField K]

def degLineS (nFin : HeightOneSpectrum (𝓞 K) → ℝ) (nInf : (K →+* ℂ) → ℝ) : ℝ :=
  -((∑ᶠ la, Real.log (nFin la)) + ∑ σ : K →+* ℂ, Real.log (nInf σ)) / (Module.finrank ℚ K : ℝ)

def LineDegreeClosedFormula (nFin : HeightOneSpectrum (𝓞 K) → ℝ) (nInf : (K →+* ℂ) → ℝ) (corr : ℝ) (p q : ℕ) (logOm dK rd : ℝ) :
    Prop :=
  degLineS K nFin nInf + corr = -(((p : ℝ) - q) / 2 * logOm + (q : ℝ) * (2 * Real.log (Real.sqrt dK) - Real.log rd))

end Formalism.NormVectorIdentities.Items
