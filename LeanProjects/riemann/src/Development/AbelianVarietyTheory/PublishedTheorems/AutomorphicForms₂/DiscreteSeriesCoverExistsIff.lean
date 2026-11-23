import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesCoverExists : Prop :=
  ∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam

end GlobalTheory.Published

end
