import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SwapCyclesArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
    (∀ U : Ideal (MRing ι), IsRelevant U → U ∈ (P ⊔ Ideal.span {s} ⊔ Ideal.span {s'}).minimalPrimes →
      ringKrullDim (MRing ι ⧸ U) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) ∧
      (U.map (Ideal.Quotient.mk P)).IsPrime ∧
      ∀ [(U.map (Ideal.Quotient.mk P)).IsPrime],
        ringKrullDim (Localization.AtPrime (U.map (Ideal.Quotient.mk P))) = 2) ∧
    (∀ W ∈ divSupp P s, ∀ U ∈ divSupp W s',
      U ∈ (P ⊔ Ideal.span {s} ⊔ Ideal.span {s'}).minimalPrimes) ∧
    ((divCycle P s).sum (fun W m => m • divCycle W s') =
      (divCycle P s').sum (fun W m => m • divCycle W s)) ∧
    ((divCycle P s).sum (fun W m => m • horCycle W s') =
      (divCycle P s').sum (fun W m => m • horCycle W s)) ∧
    ((divCycle P s).sum (fun W m => m • vertCycle W s') =
      (divCycle P s').sum (fun W m => m • vertCycle W s))

end

end GroundTheory.Heights₂.Heights.Inter
