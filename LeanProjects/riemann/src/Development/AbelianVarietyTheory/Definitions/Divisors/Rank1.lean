import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec

namespace GlobalTheory.ResW

def Rank1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (u : List (Letter E)) (x : Letter E) (t : ℝ), IsSquareIntegrableAutomorphicSpace V → SatFam V B → HasWord V u → rexp x = 0 → u.Perm [tw x (-t), tw x t] → t < 1

end GlobalTheory.ResW

end
