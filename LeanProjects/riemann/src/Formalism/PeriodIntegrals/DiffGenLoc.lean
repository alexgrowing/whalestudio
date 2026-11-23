import Mathlib

noncomputable section

namespace PI.DiffGenLoc

open NumberField IsDedekindDomain

abbrev Fv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def DiffExists : Prop := ∃ d, IsDiffVal v d

end PI.DiffGenLoc
