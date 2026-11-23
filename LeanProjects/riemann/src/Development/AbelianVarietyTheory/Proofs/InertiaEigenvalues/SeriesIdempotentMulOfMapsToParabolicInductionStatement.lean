import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentMulOfMapsToParabolicInduction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesIdempotent_mul_of_maps_to_parabolicInduction : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'), IsIrrRep π → MapsToProd π σ ρ → ∀ F, Has S π F → ∃ f f', Has S σ f ∧ Has S ρ f' ∧ F = f * f' := by
  first | exact @GlobalTheory.SerSys.Prod.series_of_mapsToProd | exact GlobalTheory.SerSys.Prod.series_of_mapsToProd | (intros; apply GlobalTheory.SerSys.Prod.series_of_mapsToProd <;> assumption)
