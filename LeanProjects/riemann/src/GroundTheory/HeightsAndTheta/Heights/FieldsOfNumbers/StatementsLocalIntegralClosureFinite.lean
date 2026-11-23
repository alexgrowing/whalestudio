import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFiniteRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def LocalIntegralClosureFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), relDim (contractPrime j P') = relDim P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ s : Finset (FractionRing (MRing ι' F ⧸ P')),
        (∀ e ∈ s, e ∈ homFracDegZero P' ∧
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) e) ∧
        ∀ x ∈ homFracDegZero P',
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) x →
          x ∈ Submodule.span ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P'))
            (s : Set (FractionRing (MRing ι' F ⧸ P')))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
