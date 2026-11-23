import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDivPushResOrderSum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsConeBranchLength
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def DivPushResBranches.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (A : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∀ᵐ y, ∀ W' ∈ divSupp P s, IsHorizontal W' → ∀ w ∈ fibre W' Ψ y,
      ∀ Wa ∈ (W'.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
      ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ f ∈ Wa, eval z f = 0) → segre z = w →
        ∃ (b : ℕ) (γ : Fin b → ConeBranch P (n + Fintype.card K + 1) z) (ord : Fin b → ℕ),
          ConeBranchesAt P s Wa z γ ord ∧
            ∑ j, ord j = ∑ᶠ x ∈ {x : R.X | projCoord R Ψ x = y ∧ divPt R Ψ x = w}, sncMult m W x

end GroundTheory.Heights₂.Heights.Targets
