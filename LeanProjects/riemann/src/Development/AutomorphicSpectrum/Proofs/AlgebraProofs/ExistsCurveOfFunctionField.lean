import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import GroundTheory.FunctionField.DivisorDegree

noncomputable section

open GroundTheory.FunctionField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isFunctionField_of_fg_trdeg {k κ : Type} [Field k] [Field κ] [Algebra k κ]
    (hfg : (⊤ : IntermediateField k κ).FG) (htr : Algebra.trdeg k κ = 1) :
    IsFunctionField k κ := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k κ
  have hcard : Cardinal.mk s = 1 := by rw [hs.cardinalMk_eq_trdeg, htr]
  obtain ⟨⟨x, hx⟩⟩ : Nonempty s := by
    rw [← Cardinal.mk_ne_zero_iff, hcard]
    exact one_ne_zero
  have hsx : s = {x} := by
    have hsub : Subsingleton s := by
      rw [← Cardinal.le_one_iff_subsingleton, hcard]
    ext y
    constructor
    · intro hy
      have := Subsingleton.elim (⟨y, hy⟩ : s) ⟨x, hx⟩
      simpa using congrArg Subtype.val this
    · rintro rfl
      exact hx
  have htrx : Transcendental k x := hs.1.transcendental ⟨x, hx⟩
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) κ := by
    have := hs.isAlgebraic_field
    rwa [Subtype.range_coe, hsx] at this
  obtain ⟨t, ht⟩ := hfg
  have hfd : ∀ F : IntermediateField k κ, Algebra.IsAlgebraic F κ → FiniteDimensional F κ := by
    intro F hF
    have hle : IntermediateField.adjoin k (↑t : Set κ) ≤
        (IntermediateField.adjoin F (↑t : Set κ)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin F _)
    have htop : IntermediateField.adjoin F (↑t : Set κ) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ IntermediateField.adjoin k (↑t : Set κ) := by
        rw [ht]
        exact IntermediateField.mem_top
      exact hle hy
    have h1 : FiniteDimensional F (IntermediateField.adjoin F (↑t : Set κ)) :=
      IntermediateField.finiteDimensional_adjoin fun y _ => (hF.isAlgebraic y).isIntegral
    rw [htop] at h1
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  exact ⟨⟨x, htrx, hfd _ halg⟩⟩

section

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsFunctionField k κ]

def placesCurve : GlobalTheory.CompanionTheory.Ar.Crv.ACurve κ where
  I := Place k κ
  v := fun i => i.valuation
  w := fun i => i.deg
  fin := fun x hx => by
    refine (Place.finite_ord_ne_zero (k := k) x).subset fun i hi h0 => hi ?_
    have h := i.valuation_eq_exp_neg_ord hx
    rw [h, h0]
    simp
  prod := fun x hx => by
    classical
    have h := Divisor.deg_divisor (k := k) x
    rw [Divisor.deg_eq_sum] at h
    rw [finsum_eq_sum_of_support_subset (s := (divisor x : Divisor k κ).support)]
    · have : ∑ i ∈ (divisor x : Divisor k κ).support,
          ((i.deg : ℤ) * WithZero.log (i.valuation x)) =
          - ∑ i ∈ (divisor x : Divisor k κ).support, (divisor x : Divisor k κ) i * (i.deg : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [divisor_apply, Place.ord]
        ring
      rw [this, h, neg_zero]
    · intro i hi
      simp only [Function.mem_support] at hi
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, divisor_apply, Place.ord]
      intro h0
      apply hi
      have : WithZero.log (i.valuation x) = 0 := by omega
      rw [this, mul_zero]

end

theorem exists_curve_of_function_field :
    ∀ (k κ : Type) [Field k] [Field κ] [Algebra k κ], (⊤ : IntermediateField k κ).FG →
      Algebra.trdeg k κ = 1 → ∃ C : GlobalTheory.CompanionTheory.Ar.Crv.ACurve κ, (∀ i, 0 < C.w i) ∧
        (∀ i (a : k), a ≠ 0 → C.v i (algebraMap k κ a) = 1) ∧
        (∀ i, Function.Surjective (C.v i)) ∧
        ∀ W : ValuationSubring κ, W ≠ ⊤ → (∀ a : k, algebraMap k κ a ∈ W) →
          ∃! i, (C.v i).valuationSubring = W := by
  intro k κ _ _ _ hfg htr
  haveI : IsFunctionField k κ := isFunctionField_of_fg_trdeg hfg htr
  have key : ∀ i : Place k κ, (i.valuation).valuationSubring = i.ring := fun i => by
    ext y
    rw [Valuation.mem_valuationSubring_iff]
    exact Place.valuation_le_one_iff i y
  refine ⟨placesCurve k κ, fun i => ?_, fun i a ha => ?_, fun i => ?_, fun W hW hk => ?_⟩
  · exact Place.deg_pos i
  · exact Place.valuation_algebraMap' i ha
  · exact Place.valuation_surjective i
  · refine ⟨⟨W, hW, hk⟩, key _, fun j hj => ?_⟩
    exact Place.ext ((key j).symm.trans hj)

end GlobalTheory.CompanionTheory.Ar.Flat
