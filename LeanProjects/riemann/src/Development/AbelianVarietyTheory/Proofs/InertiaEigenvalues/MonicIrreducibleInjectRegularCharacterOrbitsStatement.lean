import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicIrreducibleInjectRegularCharacterOrbits
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicIrreducible_inject_regularCharacterOrbits : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = d → ∃ c : (ZMod g)[X] → (Kˣ →* ℂˣ), (∀ P, IsPrimeLab d P → IsRegularChar g d (c P)) ∧ ∀ P P', IsPrimeLab d P → IsPrimeLab d P' → (∃ i < d, c P' = c P ^ g ^ i) → P = P' := by
  first | exact @GlobalTheory.PrimeLabOrbit.primeLab_to_regularChar | exact GlobalTheory.PrimeLabOrbit.primeLab_to_regularChar | (intros; apply GlobalTheory.PrimeLabOrbit.primeLab_to_regularChar <;> assumption)
