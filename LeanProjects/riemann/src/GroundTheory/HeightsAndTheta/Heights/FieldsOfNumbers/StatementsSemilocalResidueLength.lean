import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFiniteRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 400000 in

def SemilocalResidueLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
    haveI := hP'.isPrime
    ∀ W' (hW' : W' ∈ fibrePrimes j P' W),
      haveI := hW'.1.isPrime
      ∃ 𝔪 : Ideal (degZeroLoc P' (fibrePrimes j P' W)),
        (∀ x : degZeroLoc P' (fibrePrimes j P' W),
          x ∈ 𝔪 ↔ ¬ ∃ y ∈ degZeroLoc P' {W'}, (x : FractionRing (MRing ι' F ⧸ P')) * y = 1) ∧
        Module.length (degZeroLoc (contractPrime j P') {W})
            (degZeroLoc P' (fibrePrimes j P' W) ⧸ 𝔪) = (relDeg j W' : ℕ∞)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
