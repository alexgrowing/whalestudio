import ReciprocityTheory.Hypotheses.GalCohDefs

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

variable {Ω : Type} [Field Ω] (p : ℕ) [Fact p.Prime]

def Compat (A : ValuationSubring Ω) (ι : Ω →+* PadicAlgCl p) : Prop := ∀ x, x ∈ A ↔ ‖ι x‖ ≤ 1

variable {p}

def Kloc (F : Type) [Field F] [Algebra F Ω] (ι : Ω →+* PadicAlgCl p) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] (Set.range (ι.comp (algebraMap F Ω)))

abbrev GK (F : Type) [Field F] [Algebra F Ω] (ι : Ω →+* PadicAlgCl p) := PadicAlgCl p ≃ₐ[Kloc F ι] PadicAlgCl p

end ReciprocityTheory.Neutral.Cmp
