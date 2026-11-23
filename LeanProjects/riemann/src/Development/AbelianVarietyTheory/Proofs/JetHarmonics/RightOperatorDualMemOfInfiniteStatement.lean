import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfinite
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightOperatorDual_mem_of_infinite : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite → (∀ y ∈ S, rhv d y ∈ K) → ∀ y : ℂ, rhv d y ∈ K := by
  first | exact @GlobalTheory.RhvPoly.rhv_mem_of_infinite | exact GlobalTheory.RhvPoly.rhv_mem_of_infinite | (intros; apply GlobalTheory.RhvPoly.rhv_mem_of_infinite <;> assumption)
