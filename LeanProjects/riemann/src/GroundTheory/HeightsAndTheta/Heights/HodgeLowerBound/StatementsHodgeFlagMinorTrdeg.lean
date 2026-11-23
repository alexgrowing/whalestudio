import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenericMinors
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def genMat0Fr (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b => if (a : ℕ) < j ∧ j ≤ (b : ℕ) then 0 else genMatFr F Ψ n τ a b

def flagMinorRatio0 (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (q : Ψ × Σ i : Fin (n - 1), PluckerBlocks n n i) :
    GenFrac F Ψ n :=
  flagMinor (genMat0Fr F Ψ n j q.1) q.2.1 q.2.2 / leadMinor (genMat0Fr F Ψ n j q.1) q.2.1

def HodgeFlagMinorTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n j : ℕ), j ≤ n →
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio0 F Ψ n j))) =
      ((Fintype.card Ψ * (j * (j - 1) / 2 + (n - j) * (n - j - 1) / 2) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
