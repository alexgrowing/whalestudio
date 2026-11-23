import Mathlib

namespace KStar.Ram

open NumberField
open scoped Pointwise

noncomputable def vdField (E : Type*) [Field E] [NumberField E] (p : ℕ) : ℚ :=
  (padicValInt p (discr E) : ℚ) / (Module.finrank ℚ E : ℚ)

noncomputable def vdAt {E : Type*} [Field E] [NumberField E] (P : Ideal (𝓞 E)) : ℚ :=
  (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (P.ramificationIdx ℤ : ℚ)

def SplitsIn (p : ℕ) (K : Type*) [Field K] [NumberField K] : Prop :=
  ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K

noncomputable def conjIdeal {E : Type*} [Field E] [NumberField E] [IsCMField E]
    (I : Ideal (𝓞 E)) : Ideal (𝓞 E) :=
  I.map (IsCMField.ringOfIntegersComplexConj E)

end KStar.Ram
