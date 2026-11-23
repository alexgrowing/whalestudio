import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedOfLevelAwayInertiaCharacters
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondIffRhoOfGoodPoint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_of_levelAway_inertia_characters : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (M : ℕ), 1 ≤ M → LevelAway l M W → ∃ S : Finset Pl, ContainsAbove S l ∧ ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker := by
  first | exact @GlobalTheory.Ord2.unramified_of_levelAway | exact GlobalTheory.Ord2.unramified_of_levelAway | (intros; apply GlobalTheory.Ord2.unramified_of_levelAway <;> assumption)
