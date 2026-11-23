import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeStepCoordinateVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.LieRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_step_coordinate_vectors : ∀ (D : D7) (O : Setup D) (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = (letters O.S.Dw).length → ∀ (τ : D.host.E →+* ℂ) (i : ℕ), i < O.S.Dw.mult τ → ∃ p : Fin (i + 1) → Fin F.P₀.g, Function.Injective p ∧ (∀ j : Fin (i + 1), stepVec O F τ j = Pi.single (p j) 1) ∧ (∀ v, stepCoef O F τ i v = v (p (Fin.last i))) ∧ stepLat O F τ (i + 1) = F.lieLat ⊓ (Submodule.span K (Set.range fun j => (Pi.single (p j) 1 : Fin F.P₀.g → K))).restrictScalars (𝓞 K) ∧ stepLat O F τ i = F.lieLat ⊓ (Submodule.span K (Set.range fun j : Fin i => (Pi.single (p j.castSucc) 1 : Fin F.P₀.g → K))).restrictScalars (𝓞 K) := by
  first | exact @GlobalTheory.LieRead.stepVec_letters | exact GlobalTheory.LieRead.stepVec_letters | (intros; apply GlobalTheory.LieRead.stepVec_letters <;> assumption)
