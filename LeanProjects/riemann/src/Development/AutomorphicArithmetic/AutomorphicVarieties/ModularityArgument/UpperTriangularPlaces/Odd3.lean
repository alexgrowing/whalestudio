import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OddAOfUnl

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {M : ℕ}
  {m : Fin 3 → ℤ} {r : G F Ω →* GL (Fin 3) (Qbar l)}

theorem UpperTheory.V.Keep.odd3' (h : Th.Unl l M m r) : Keep.OddA l r := Keep.oddA_of_unl h
