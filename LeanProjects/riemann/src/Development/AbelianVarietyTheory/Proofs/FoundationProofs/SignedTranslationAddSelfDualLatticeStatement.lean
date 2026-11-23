import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignedTranslationAddSelfDualLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedTranslation_add_selfDual_lattice : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → (∀ x ∈ A, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A, w0 D • x ∈ A) → ∀ x ∈ A, ∀ y ∈ A, al D T (x + y) = al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) := by
  first | exact @GlobalTheory.GalTheta.al_add | exact GlobalTheory.GalTheta.al_add | (intros; apply GlobalTheory.GalTheta.al_add <;> assumption)
