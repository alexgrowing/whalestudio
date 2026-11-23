import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsConeBranchLength
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def ConeComplexBaseChange.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (s : MRing ι) (W' : Ideal (MRing ι)) (Wa : Ideal (MRingOver ℂ ι)),
    IsArithVar P (n + 2) → s ∉ P → W' ∈ divSupp P s → IsHorizontal W' →
    Wa ∈ (W'.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
      (P.map (MvPolynomial.map (Int.castRingHom ℂ))).IsRadical ∧
      (∀ Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
        ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ∧
          MvPolynomial.map (Int.castRingHom ℂ) s ∉ Q) ∧
      Wa ∈ ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Targets
