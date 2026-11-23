import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycEval_eq_sum {K : Type} {ι : K → Type} {R : Type} [CommRing R]
    (n Z : Ideal (MRing ι R) → ℤ) (T : Finset (Ideal (MRing ι R)))
    (hT : Function.support Z ⊆ (T : Set (Ideal (MRing ι R)))) :
    cycEval n Z = ∑ W ∈ T, Z W * n W := by
  unfold cycEval
  refine finsum_eq_sum_of_support_subset _ ?_
  intro W hW
  apply hT
  intro h0
  apply hW
  simp [h0]

theorem cycEval_comb {K : Type} {ι : K → Type} {R : Type} [CommRing R]
    (n : Ideal (MRing ι R) → ℤ) {α : Type} (s : Finset α) (c : α → ℤ)
    (Z : α → Ideal (MRing ι R) → ℤ) (hZ : ∀ a, (Function.support (Z a)).Finite) :
    cycEval n (fun W => ∑ a ∈ s, c a * Z a W) = ∑ a ∈ s, c a * cycEval n (Z a) := by
  classical
  set T : Finset (Ideal (MRing ι R)) := s.biUnion fun a => (hZ a).toFinset with hTdef
  have hsum : Function.support (fun W => ∑ a ∈ s, c a * Z a W) ⊆
      (T : Set (Ideal (MRing ι R))) := by
    intro W hW
    by_contra hWT
    apply hW
    refine Finset.sum_eq_zero fun a ha => ?_
    have : Z a W = 0 := by
      by_contra hne
      exact hWT (by
        simp only [hTdef, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
          Set.Finite.coe_toFinset]
        exact ⟨a, ha, hne⟩)
    simp [this]
  have hone : ∀ a ∈ s, cycEval n (Z a) = ∑ W ∈ T, Z a W * n W := by
    intro a ha
    refine cycEval_eq_sum n (Z a) T ?_
    intro W hW
    simp only [hTdef, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Set.Finite.coe_toFinset]
    exact ⟨a, ha, hW⟩
  have hrhs : ∑ a ∈ s, c a * cycEval n (Z a) = ∑ a ∈ s, c a * ∑ W ∈ T, Z a W * n W :=
    Finset.sum_congr rfl fun a ha => by rw [hone a ha]
  rw [cycEval_eq_sum n _ T hsum, hrhs]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun W _ => ?_
  ring

theorem cycNum_int_and_comb : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ (Z : Ideal (MRing ι O) → ℤ), (Function.support Z).Finite → ∀ H : MvPolynomial σ ℤ, cycNum Z cls (MvPolynomial.map (Int.castRingHom ℝ) H) Q = ((cycEval (fun W => classNum cls H Q W) Z : ℤ) : ℝ)) ∧ (∀ (α : Type) (s : Finset α) (c : α → ℤ) (Z : α → Ideal (MRing ι O) → ℤ), (∀ a, (Function.support (Z a)).Finite) → ∀ H : MvPolynomial σ ℝ, cycNum (fun W => ∑ a ∈ s, c a * Z a W) cls H Q = ∑ a ∈ s, (c a : ℝ) * cycNum (Z a) cls H Q) := by
  intro O _ _ _ K _ _ ι _ σ cls Q
  refine ⟨?_, ?_⟩
  · intro Z hZ H
    have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
    have hT : Function.support Z ⊆ (hZ.toFinset : Set (Ideal (MRing ι O))) := by simp
    have key : cycEval (fun W => classNum cls H Q W) Z =
        ∑ μ ∈ H.support, H.coeff μ * cycList Z (classList cls μ ++ Q) := by
      unfold cycList
      rw [cycEval_eq_sum _ Z _ hT]
      simp only [cycEval_eq_sum _ Z _ hT, classNum, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
      ring
    unfold cycNum
    rw [MvPolynomial.support_map_of_injective _ hinj, key]
    push_cast
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.coeff_map]
    simp
  · intro α s c Z hZ H
    unfold cycNum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have : cycList (fun W => ∑ a ∈ s, c a * Z a W) (classList cls μ ++ Q) =
        ∑ a ∈ s, c a * cycList (Z a) (classList cls μ ++ Q) :=
      cycEval_comb _ s c Z hZ
    rw [this]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.CompanionTheory.Ar.Num
