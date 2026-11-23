import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Af

namespace UpperTheory.V.X

def LemmaKato : Prop :=
  ∀ (e : ℕ), 1 ≤ e → ∀ (g : Newform (2 * e + 1)) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous V → g.Att ι V →
    ∀ (M : ℕ), 1 ≤ M → ∀ φ : G ℚ Ω →* (Qbar l)ˣ, KillsMu M φ →
      BlochKatoSelmerVanishes l (Loc.colRep (tw V (cycBar ℚ Ω l ^ e * φ)))

def LemmaKatoW : Prop :=
  ∀ (e : ℕ), 1 ≤ e → ∀ (g : Newform (2 * e + 1)) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
    ∀ (M : ℕ), 1 ≤ M → ∀ φ : G ℚ Ω →* (Qbar l)ˣ, KillsMu M φ →
      g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * φ)) → BlochKatoSelmerVanishes l (Loc.colRep W)

end UpperTheory.V.X
