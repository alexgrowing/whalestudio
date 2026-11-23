import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FlatTheorem

open NumberField

noncomputable def rootDisc (F : Type*) [Field F] [NumberField F] : ℝ :=
  |(discr F : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ F : ℝ))

theorem rootDisc_rat : rootDisc ℚ = 1 := by
  simp [rootDisc]

def RootDiscriminantMonotone.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E],
    rootDisc K ≤ rootDisc E

theorem RootDiscriminantMonotone.inhabitant : Nonempty (Algebra ℚ (CyclotomicField 4 ℚ)) :=
  ⟨inferInstance⟩

structure FlatDegreeFormula (K E : Type*) [Field K] [NumberField K] [Field E]
    [NumberField E] where

  p : ℕ

  q' : ℕ

  logOm : ℝ

  d : ℝ

  formula : d = ((p : ℝ) - q') / 2 * logOm +
    q' * (2 * Real.log (rootDisc K) - Real.log (rootDisc E))

noncomputable def FlatDegreeFormula.inhabitant : FlatDegreeFormula ℚ (CyclotomicField 4 ℚ) where
  p := 2
  q' := 1
  logOm := 1
  d := (((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 2 * 1 +
    ((1 : ℕ) : ℝ) * (2 * Real.log (rootDisc ℚ) - Real.log (rootDisc (CyclotomicField 4 ℚ)))
  formula := rfl

def FlatDegreeBound.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (D : FlatDegreeFormula K E),
    |-D.d + ((D.p : ℝ) - D.q') / 2 * D.logOm| ≤ D.q' * Real.log (rootDisc E)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FlatTheorem
