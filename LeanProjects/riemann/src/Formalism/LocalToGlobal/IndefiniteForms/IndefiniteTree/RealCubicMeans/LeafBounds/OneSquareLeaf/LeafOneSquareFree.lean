import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive

noncomputable section

open NumberField
open IsDedekindDomain
open Finset
open Formalism.PairingDivisionLocalBalance (wt HtLe meanInf)
open Formalism.HN (muMaxDef htMap)
open Formalism.DivisionValues
open Formalism.L2.Indef
open Formalism.L2.Indef.Tree

namespace Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

def SquareCoefficientsCondition {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} {Sq : Type}
    (r0 : Fin m × Fin m → K) (rw : Formalism.PairingDivisionLocalBalance.Pl K → Fin m × Fin m → K) (Se Sd : Finset ℕ) (dd hd yy : Fin m × Fin m → ℕ)
    (N : ℕ) (S0 : Finset Sq) (cc qq ee : Sq → ℕ) (zA zA' : Fin m × Fin m → K) (zT : Fin m × Fin m → ℤ → K)
    (zTd : Fin m × Fin m → Bool → ℤ → K) (gT : Fin m × Fin m → ℤ → Formalism.PairingDivisionLocalBalance.Pl K → ℤ) (ch : Formalism.PairingDivisionLocalBalance.Pl K → Bool)
    (N0 : Fin m × Fin m → ℤ → ℕ → ℝ) (dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ) : Prop :=
  (∀ ij, r0 ij = 1) ∧ (∀ w ij, rw w ij ≠ 0) ∧ (∀ l ∈ Se, l.Prime) ∧
    (∀ ij, dd ij = 2 * hd ij) ∧ (∀ ij, dd ij ≤ 2 * N) ∧ (∀ ij, yy ij + 1 ≤ m) ∧
    (∀ q ∈ S0, cc q ≤ ee q) ∧
    ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, ∀ ij, (vw w (rw w ij) : ℝ) ≤ |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| +
      4 * (∑ s ∈ Finset.Icc (1 : ℤ) (hd ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) +
      5 * (∑ s ∈ Finset.Icc (1 : ℤ) (hd ij), wt Sd (N0 ij s) w) +
      dd ij * wt Se (fun l => 1 / (l : ℝ) ^ 2) w + 6 * dl w +
      yy ij * (2 * ∑ q ∈ S0, (cc q : ℝ) * (vw w (qq q : K) : ℝ))

end Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
