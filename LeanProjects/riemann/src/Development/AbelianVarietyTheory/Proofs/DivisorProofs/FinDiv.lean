import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.FinSupp

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable (F : Type) [Field F] [NumberField F]

def FinDiv (N : ℕ) (a : AF F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ b ∈ v.adicCompletionIntegers F, evFin F v a = (N : Fv F v) * b

def finPart (a : AF F) : AF F := (0, a.2)

end GlobalTheory.FinSupp
