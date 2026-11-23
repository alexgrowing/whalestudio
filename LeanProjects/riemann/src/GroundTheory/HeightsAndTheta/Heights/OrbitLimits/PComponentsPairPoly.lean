import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem exists_pair_poly {n d : ℕ} (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hJJ' : ¬ J' ≤ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ x ∈ zeroSet J, x ∈ zeroSet J' → eval (A *ᵥ x) c = 0 := by
  obtain ⟨f, hfJ', hfJ⟩ := SetLike.not_le_iff_exists.1 hJJ'
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  have := hJ
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) := hA.finite.to_isIntegral _
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨c, hc0, fun x hx hx' => ?_⟩
  have h1 : Ideal.Quotient.mk J (pullback A c) = Ideal.Quotient.mk J (r * f) := by
    rw [map_mul]; exact hr.symm
  have h2 := hx _ (Ideal.Quotient.eq.1 h1)
  rwa [map_sub, map_mul, hx' f hfJ', mul_zero, sub_zero, ComplexSets.FibreBound.eval_pullback] at h2

theorem encard_biUnion_le {ι α : Type*} (F : Finset ι) (S : ι → Set α) :
    (⋃ i ∈ F, S i).encard ≤ ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (by gcongr)

theorem encard_biUnion_eq {ι α : Type*} (F : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j)) :
    (⋃ i ∈ F, S i).encard = ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ih]
    · exact fun i hi j hj hij =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    · refine Set.disjoint_iUnion₂_right.2 fun j hj =>
        h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) ?_
      rintro rfl
      exact ha hj

theorem exists_prod_ne_zero {ι : Type*} {k : ℕ} (F : Finset ι) (p : ι → MvPolynomial (Fin k) ℂ → Prop)
    (h : ∀ i ∈ F, ∃ P, P ≠ 0 ∧ p i P) :
    ∃ Δ : MvPolynomial (Fin k) ℂ, Δ ≠ 0 ∧
      ∀ y, eval y Δ ≠ 0 → ∀ i ∈ F, ∃ P, p i P ∧ eval y P ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨Δ, hΔ, hΔy⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨P, hP, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨P * Δ, mul_ne_zero hP hΔ, fun y hy i hi => ?_⟩
    rw [map_mul] at hy
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨P, hPa, left_ne_zero_of_mul hy⟩
    · exact hΔy y (right_ne_zero_of_mul hy) i hi

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
