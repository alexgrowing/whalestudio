import Formalism.SharpRestriction.GrowthBounds.RootWeights.StableSubspaceCompleteReducibility

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

open Classical in

def letterPolarizationDerivation (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    Derivation R (MvPolynomial (ι × Fin n) R) (MvPolynomial (ι × Fin n) R) :=
  ∑ l : ι,
    if l ∈ S then
      (if LL.vec l then (X (l, a) : MvPolynomial (ι × Fin n) R) • pderiv (l, b)
       else -((X (l, b) : MvPolynomial (ι × Fin n) R) • pderiv (l, a)))
    else 0

theorem v2con_sum_apply {R : Type*} [CommRing R] {σ : Type*} {α : Type*} (s : Finset α)
    (f : α → Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (F : MvPolynomial σ R) :
    (∑ i ∈ s, f i) F = ∑ i ∈ s, f i F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

theorem v2con_glAct_eq {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (F : MvPolynomial (ι × Fin n) R) : glAct R LL S a b F = letterPolarizationDerivation R LL S a b F := by
  unfold glAct letterPolarizationDerivation
  rw [LinearMap.sum_apply, v2con_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

open Classical in
theorem v2con_der_X {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (l : ι) (c : Fin n) : letterPolarizationDerivation R LL S a b (X (l, c)) =
      if l ∈ S then
        (if LL.vec l then (if c = b then X (l, a) else 0) else (if c = a then -X (l, b) else 0))
      else 0 := by
  unfold letterPolarizationDerivation
  rw [v2con_sum_apply, Finset.sum_eq_single l]
  · split_ifs <;> simp_all [pderiv_X, Pi.single_apply]
  · intro l' _ hl'
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hl']
  · simp

end Formalism.MainNotions.G.GLWeightTheory
