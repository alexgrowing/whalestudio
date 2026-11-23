import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.GenDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTors

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.genIff :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G k Ω)) (R : ℕ), IsClosed (U : Set (G k Ω)) → (GenLE ℤ_[l] (Xinf l N U) R ↔ xRank l N U ≤ R) := by
  intro k Ω _ _ _ _ _ l _ N U R hU
  exact UpperTheory.V.Tower.genDual l (Dinf l N U) R ((UpperTheory.V.Tower.dinfTors k Ω l N U).1 hU)
