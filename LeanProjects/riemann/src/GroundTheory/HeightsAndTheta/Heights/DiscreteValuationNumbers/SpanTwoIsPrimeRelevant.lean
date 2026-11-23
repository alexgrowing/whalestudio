import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtPrimeAtMinimal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def commonExcess (ϖ : O) (P : Ideal (MRing ι O)) (f g s : MRing ι O) : ℕ :=
  ⨆ G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G}, (divCycle P s G.1 * ratDiv P f g G.1).toNat

end Defs

section Lemmas

def NoCommonComponentCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

def CommonFactorInduction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P s G ≠ 0 ∧ ratDiv P f g G ≠ 0) →
    (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (P' : Ideal (MRing ι' O)) (d' : ℕ), IsModelOver P' (d' + 1) →
      ∀ (b' : K' → ℤ) (f' g' : MRing ι' O), IsEffectiveVertical P' ϖ b' f' g' →
      ∀ (c' : K' → ℕ) (s' : MRing ι' O), IsMultiHomog s' c' → s' ∉ P' →
      (∀ H, divCycle P' s' H ≠ 0 → (C ϖ : MRing ι' O) ∉ H → IsVerticalDivisor H ϖ b' f' g') →
      commonExcess ϖ P' f' g' s' < commonExcess ϖ P f g s →
      ∀ L' : Fin d' → K' → ℤ, cutIdentity ϖ P' b' f' g' c' s' L') →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
