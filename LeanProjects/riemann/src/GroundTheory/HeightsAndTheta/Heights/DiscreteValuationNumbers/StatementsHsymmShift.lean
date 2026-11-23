import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumRatSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def HsymmShift.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
    ∀ d : ℕ, FieldNumbers.relDim W = (d : WithBot (WithTop ℤ)) →
    ∀ (N : ℕ), 0 < N → ∀ (x : Fin N → K → ℤ) (s : K → ℤ) (r : ℕ) (Y : List (K → ℤ)),
      r + Y.length = d →
      ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (fun i => x i + s) α ++ Y) =
        ∑ k ∈ Finset.range (r + 1), ((N - 1 + r).choose k : ℤ) *
          ∑ α ∈ Finset.Nat.antidiagonalTuple N (r - k),
            intNumL F W (rootList x α ++ List.replicate k s ++ Y)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
