import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.CorA3primeB
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathBasisOfCount
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace SpanImageLemmas

theorem split {X R : Type} [CommRing R] (a : X →₀ R) (S : Set X) :
    ∃ a1 a2 : X →₀ R, a = a1 + a2 ∧ (∀ x ∉ S, a1 x = 0) ∧ (∀ x ∈ S, a2 x = 0) ∧ ∀ x ∉ S, a2 x = a x := by
  classical
  refine ⟨a.filter (· ∈ S), a.filter (fun x => ¬ x ∈ S), (Finsupp.filter_add_filter_not a _).symm, ?_, ?_, ?_⟩
  · intro x hx
    exact Finsupp.filter_apply_neg _ _ hx
  · intro x hx
    exact Finsupp.filter_apply_neg _ _ (not_not.mpr hx)
  · intro x hx
    exact Finsupp.filter_apply_pos _ _ hx

variable {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}

theorem basis (hc : CountPAll) (h2 : PathBasisOfCount) (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) :
    LinearIndependent R (psiFam R n N isVec B) ∧
      Submodule.span R (Set.range (psiFam R n N isVec B)) = polB R n N B :=
  h2 n N isVec B (hc n N isVec B) R

def good (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : ℕ → WithBot ℤ) (M : ℕ → WithTop ℤ) :
    Set (PathIdx n N isVec B) :=
  {x | ∀ i ≤ N, GoodW (θ i) (M i) (x.1.1 i)}

end SpanImageLemmas

open SpanImageLemmas

namespace SpanImageLemmas

variable {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}

end SpanImageLemmas

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
