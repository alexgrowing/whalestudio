import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

noncomputable def conjLinearCombination {M : Type} [AddCommGroup M] [Module ℂ M] {I : Type}
    (b : I → M) : (I →₀ ℂ) →ₗ⋆[ℂ] M where
  toFun c := c.sum fun i x => star x • b i
  map_add' c d := by
    rw [Finsupp.sum_add_index']
    · intro i; simp
    · intro i x y; rw [star_add, add_smul]
  map_smul' r c := by
    rw [Finsupp.sum_smul_index' (by intro i; simp), Finsupp.smul_sum]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [smul_smul, smul_eq_mul, star_mul', starRingEnd_apply]

theorem conjLinearCombination_single {M : Type} [AddCommGroup M] [Module ℂ M] {I : Type}
    (b : I → M) (i : I) (x : ℂ) :
    conjLinearCombination b (Finsupp.single i x) = star x • b i := by
  change (Finsupp.single i x).sum (fun i x => star x • b i) = _
  rw [Finsupp.sum_single_index]; simp

theorem exists_conjLinear_of_gram_eq :
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Type) [AddCommGroup M] [Module ℂ M] (N : M → M → ℂ) (I : Type) (a : I → W) (b : I → M), (∀ p p' q, N (p + p') q = N p q + N p' q) → (∀ (c : ℂ) p q, N (c • p) q = c * N p q) → (∀ p q, N q p = star (N p q)) → (∀ p, N p p = 0 → p = 0) → Submodule.span ℂ (Set.range a) = ⊤ → (∀ i j, N (b j) (b i) = ⟪a j, a i⟫_ℂ) → ∃ Jm : W →ₗ⋆[ℂ] M, (∀ i, Jm (a i) = b i) ∧ ∀ ξ η, N (Jm η) (Jm ξ) = ⟪η, ξ⟫_ℂ := by
  intro W _ _ M _ _ N I a b hadd hsmul hstar hdef hspan hgram
  have hadd2 : ∀ p q q', N p (q + q') = N p q + N p q' := by
    intro p q q'
    rw [hstar (q + q') p, hadd, star_add, ← hstar, ← hstar]
  have hsmul2 : ∀ (c : ℂ) p q, N p (c • q) = star c * N p q := by
    intro c p q
    rw [hstar (c • q) p, hsmul, star_mul', ← hstar]
  have hz1 : ∀ q, N 0 q = 0 := by
    intro q
    have := hsmul 0 0 q
    simpa using this
  have hz2 : ∀ p, N p 0 = 0 := by
    intro p
    rw [hstar 0 p, hz1, star_zero]
  set A := Finsupp.linearCombination ℂ a with hA
  set B := conjLinearCombination b with hB
  have key : ∀ c d, N (B c) (B d) = ⟪A c, A d⟫_ℂ := by
    intro c d
    induction c using Finsupp.induction_linear with
    | zero => simp [hz1]
    | add c c' h h' => rw [map_add, map_add, hadd, inner_add_left, h, h']
    | single i x =>
      induction d using Finsupp.induction_linear with
      | zero => simp [hz2]
      | add d d' h h' => rw [map_add, map_add, hadd2, inner_add_right, h, h']
      | single j y =>
        rw [hA, hB, conjLinearCombination_single, conjLinearCombination_single,
          Finsupp.linearCombination_single, Finsupp.linearCombination_single, hsmul, hsmul2,
          inner_smul_left, inner_smul_right, hgram, star_star, starRingEnd_apply]
  have hr : LinearMap.range A = ⊤ := by
    rw [hA, Finsupp.range_linearCombination, hspan]
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective A hr
  have hs' : ∀ w, A (s w) = w := fun w => LinearMap.congr_fun hs w
  refine ⟨B.comp s, fun i => ?_, fun ξ η => ?_⟩
  · have h0 : B (s (a i) - Finsupp.single i 1) = 0 := by
      apply hdef
      have : A (s (a i) - Finsupp.single i 1) = 0 := by
        rw [map_sub, hs', hA, Finsupp.linearCombination_single, one_smul, sub_self]
      rw [key, this, inner_zero_left]
    rw [map_sub, sub_eq_zero, hB, conjLinearCombination_single, star_one, one_smul] at h0
    exact h0
  · change N (B (s η)) (B (s ξ)) = _
    rw [key, hs', hs']

end GlobalTheory
