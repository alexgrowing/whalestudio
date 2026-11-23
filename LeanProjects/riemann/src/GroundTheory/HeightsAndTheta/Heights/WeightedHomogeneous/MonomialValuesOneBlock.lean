import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise

noncomputable section

namespace SpanningAtDominantWeight

theorem exists_le_sum_eq {α : Type} [Fintype α] (f : α → ℕ) :
    ∀ a : ℕ, a ≤ ∑ i, f i → ∃ g : α → ℕ, g ≤ f ∧ ∑ i, g i = a := by
  classical
  intro a
  induction a with
  | zero => exact fun _ ↦ ⟨0, fun _ ↦ Nat.zero_le _, by simp⟩
  | succ a ih =>
    intro ha
    obtain ⟨g, hg, hs⟩ := ih (by omega)
    have hex : ∃ i, g i < f i := by
      by_contra h
      push Not at h
      have : ∑ i, f i ≤ ∑ i, g i := Finset.sum_le_sum fun i _ ↦ h i
      omega
    obtain ⟨i, hi⟩ := hex
    refine ⟨Function.update g i (g i + 1), fun j ↦ ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        omega
      · simp only [Function.update_of_ne hj]
        exact hg j
    · rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)] at hs
      omega

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem exists_split (μ : Coord n →₀ ℕ) (d e : ι → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = d k + e k) :
    ∃ μ₁ μ₂ : Coord n →₀ ℕ, μ = μ₁ + μ₂ ∧ (∀ k, ∑ i, μ₁ ⟨k, i⟩ = d k) ∧ ∀ k, ∑ i, μ₂ ⟨k, i⟩ = e k := by
  classical
  choose g hg hs using fun k ↦
    exists_le_sum_eq (fun i : Fin (n k + 1) ↦ μ ⟨k, i⟩) (d k) (by rw [hμ k]; omega)
  let μ₁ : Coord n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p ↦ g p.1 p.2
  have h₁ : ∀ p, μ₁ p = g p.1 p.2 := fun p ↦ rfl
  refine ⟨μ₁, μ - μ₁, ?_, fun k ↦ ?_, fun k ↦ ?_⟩
  · ext p
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, h₁]
    have : g p.1 p.2 ≤ μ p := hg p.1 p.2
    omega
  · simp only [h₁]
    exact hs k
  · have hsplit : ∑ i, μ ⟨k, i⟩ = ∑ i, g k i + ∑ i, (μ - μ₁) ⟨k, i⟩ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Finsupp.tsub_apply, h₁]
      have : g k i ≤ μ ⟨k, i⟩ := hg k i
      omega
    have := hμ k
    have := hs k
    omega

theorem prod_pow_add {M : Type} [CommMonoid M] (z : Coord n → M) (μ₁ μ₂ : Coord n →₀ ℕ) :
    ∏ p, z p ^ (μ₁ + μ₂) p = (∏ p, z p ^ μ₁ p) * ∏ p, z p ^ μ₂ p := by
  simp [pow_add, Finset.prod_mul_distrib]

theorem aeval_monomial_one {R : Type} [CommRing R] (z : Coord n → R) (μ : Coord n →₀ ℕ) :
    aeval z (monomial μ (1 : ℤ)) = ∏ p, z p ^ μ p := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_one, one_mul]

omit [Fintype ι] in

theorem isMultiHomog_monomial (μ : Coord n →₀ ℕ) (d : ι → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = d k) :
    Geo.IsMultiHomog (ι := blockIdx n) (monomial μ (1 : ℤ)) d := by
  classical
  intro m hm k
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  subst this
  exact hμ k

theorem secM_eq_span {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) :
    Geo.secM (ι := blockIdx n) y d = (Submodule.span ℤ (monomialValues y d)).toAddSubgroup := by
  unfold Geo.secM
  congr 1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro s ⟨g, hg, rfl⟩
    rw [g.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm ↦ ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hg m hm, rfl⟩)
  · rw [Submodule.span_le]
    rintro s ⟨μ, hμ, rfl⟩
    exact Submodule.subset_span ⟨monomial μ 1, isMultiHomog_monomial μ d hμ, aeval_monomial_one y μ⟩

theorem monomialValues_add {Ω : Type} [Field Ω] (y : Coord n → Ω) (d e : ι → ℕ) :
    monomialValues y (d + e) = monomialValues y d * monomialValues y e := by
  ext s
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    obtain ⟨μ₁, μ₂, rfl, h₁, h₂⟩ := exists_split μ d e hμ
    exact Set.mem_mul.mpr ⟨_, ⟨μ₁, h₁, rfl⟩, _, ⟨μ₂, h₂, rfl⟩, (prod_pow_add y μ₁ μ₂).symm⟩
  · intro hs
    obtain ⟨_, ⟨μ₁, h₁, rfl⟩, _, ⟨μ₂, h₂, rfl⟩, rfl⟩ := Set.mem_mul.mp hs
    exact ⟨μ₁ + μ₂, fun k ↦ by simp [Finset.sum_add_distrib, h₁, h₂], (prod_pow_add y μ₁ μ₂).symm⟩

theorem monomialValues_nsmul {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) (τ : ℕ) :
    monomialValues y (τ • d) = monomialValues y d ^ τ := by
  induction τ with
  | zero => rw [zero_smul, monomialValues_zero, pow_zero, Set.singleton_one]
  | succ τ ih => rw [succ_nsmul, monomialValues_add, ih, pow_succ]

theorem monomialValues_one_block {Ω : Type} [Field Ω] (m : ℕ) (x' : Fin (m + 1) → Ω) :
    monomialValues (n := fun _ : Unit ↦ m) (fun p ↦ x' p.2) (fun _ ↦ 1) = Set.range x' := by
  classical
  ext s
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have hsum : ∑ i, μ ⟨(), i⟩ = 1 := hμ ()
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsum
    have hj1 : μ ⟨(), j⟩ = 1 := by omega
    have hrest := Finset.sum_eq_zero_iff.mp (by omega : ∑ i ∈ Finset.univ.erase j, μ ⟨(), i⟩ = 0)
    refine ⟨j, ?_⟩
    rw [Fintype.prod_eq_single (⟨(), j⟩ : Coord fun _ : Unit ↦ m)]
    · simp [hj1]
    · rintro ⟨⟨⟩, i⟩ hi
      have hij : i ≠ j := fun h ↦ hi (h ▸ rfl)
      rw [hrest i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩), pow_zero]
  · rintro ⟨j, rfl⟩
    refine ⟨Finsupp.single ⟨(), j⟩ 1, fun k ↦ ?_, ?_⟩
    · simp [Finsupp.single_apply]
    · rw [← Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_single_index (by simp)]
      simp

theorem monomial_bound {Q : Ideal (MvPolynomial (Coord n) ℤ)} {A : Geo.HermLine (blockIdx n)} {b : ι → ℕ}
    (hA : Geo.MonomialsBounded (ι := blockIdx n) Q A b) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) Q) :
    ∀ τ : ℕ, ∀ μ : Coord n →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) → ‖∏ p, z p ^ μ p‖ ≤ A.h z ^ τ := by
  intro τ
  induction τ with
  | zero =>
    intro μ hμ
    have h0 : ∀ p, μ p = 0 := fun p ↦ by
      have := hμ p.1
      rw [zero_smul, Pi.zero_apply, Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  | succ τ ih =>
    intro μ hμ
    obtain ⟨μ₁, μ₂, rfl, h₁, h₂⟩ := exists_split μ (τ • b) b (fun k ↦ by rw [hμ k, succ_nsmul]; rfl)
    rw [prod_pow_add, norm_mul, pow_succ]
    exact mul_le_mul (ih μ₁ h₁) (hA z hz μ₂ h₂) (norm_nonneg _) (pow_nonneg (A.pos z hz.1).le _)

theorem isSmallH_monomial {Ω : Type} [Field Ω] (y : Coord n → Ω) (A : Geo.HermLine (blockIdx n)) (b : ι → ℕ)
    (hAa : ∀ k, A.a k = b k)
    (hA : Geo.MonomialsBounded (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) A b) (τ : ℕ)
    (μ : Coord n →₀ ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) :
    Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) y A τ (∏ p, y p ^ μ p) := by
  intro dg dh g h z hg hh hd hgh hz
  have hdeg : dg = τ • b + dh := by
    funext k
    have := hd k
    rw [hAa k] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast (by linarith : (dg k : ℤ) = τ * b k + dh k)
  have hmh := LowerBoundFree.isMultiHomog_mul (isMultiHomog_monomial μ (τ • b) hμ) hh
  rw [← hdeg] at hmh
  have hneg : Geo.IsMultiHomog (ι := blockIdx n) (-(monomial μ (1 : ℤ) * h)) dg :=
    fun m hm ↦ hmh m (by simpa using hm)
  have hF := LowerBoundFree.isMultiHomog_add hg hneg
  have hF0 : aeval y (g + -(monomial μ (1 : ℤ) * h)) = 0 := by
    rw [map_add, map_neg, map_mul, aeval_monomial_one, hgh]
    ring
  have hz0 := hz.2 _ (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
  have hmz : eval z (map (Int.castRingHom ℂ) (monomial μ (1 : ℤ))) = ∏ p, z p ^ μ p := by
    rw [map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_one, one_mul]
  rw [map_add, map_neg, map_mul, eval_add, eval_neg, eval_mul, hmz, add_neg_eq_zero] at hz0
  rw [hz0, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (monomial_bound hA hz τ μ hμ) (norm_nonneg _)

end SpanningAtDominantWeight

theorem SpanningAtDominantWeight.proof : SpanningAtDominantWeight.Statement := by
  intro ι _ _ n Ω _ y b m x' hx' τ
  have hτ : (fun _ : Unit ↦ τ) = τ • fun _ : Unit ↦ 1 := by
    funext
    simp
  refine ⟨?_, SpanningAtDominantWeight.secM_eq_span y (τ • b), fun A Q hA z hz μ hμ ↦ SpanningAtDominantWeight.monomial_bound hA hz τ μ hμ,
    fun A hAa hA μ hμ ↦ SpanningAtDominantWeight.isSmallH_monomial y A b hAa hA τ μ hμ⟩
  rw [SpanningAtDominantWeight.secM_eq_span, SpanningAtDominantWeight.secM_eq_span, hτ, SpanningAtDominantWeight.monomialValues_nsmul,
    SpanningAtDominantWeight.monomialValues_one_block, SpanningAtDominantWeight.monomialValues_nsmul, ← Submodule.span_pow, ← Submodule.span_pow, hx']

end

end GroundTheory.Heights₂.Heights
