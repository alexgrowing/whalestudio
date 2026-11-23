import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

open Classical in

def MixedTwistShift.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (qq : Ideal (Poly k N)), qq.IsPrime → (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) →
    primeOf (S := k) x ≤ qq → ringKrullDim (Poly k N ⧸ qq) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) →
    ∀ (L : Fin n → LineBundle k x) (M : LineBundle k x) (d : ℤ), ∀ᶠ c : ℕ in atTop,
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
          restrLen qq (((tensorSub (fun i => (L i).toSubSystem) T).twist M.toSubSystem).twist
            (twistSys k x ((c : ℤ) + d))) =
        if IsSubvar x qq n then interNum qq (fun i => (L i).toSubSystem) else 0

theorem mixedTwistShift_hyps (k : Type u) [Field k] :
    (primeOf (S := k) (genericPt k 1)).IsPrime ∧
      (∀ f ∈ primeOf (S := k) (genericPt k 1), ∀ d : ℕ,
        homogeneousComponent d f ∈ primeOf (S := k) (genericPt k 1)) ∧
      primeOf (S := k) (genericPt k 1) ≤ primeOf (S := k) (genericPt k 1) ∧
      ringKrullDim (Poly k 1 ⧸ primeOf (S := k) (genericPt k 1)) ≤ ((1 + 1 : ℕ) : WithBot ℕ∞) ∧
      Nonempty (Fin 1 → LineBundle k (genericPt k 1)) :=
  ⟨(isSubvar_genericPt k 1).isPrime, (isSubvar_genericPt k 1).homog, le_rfl,
    (isSubvar_genericPt k 1).dim.le, ⟨![twistBundle k (genericPt k 1) 1]⟩⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
