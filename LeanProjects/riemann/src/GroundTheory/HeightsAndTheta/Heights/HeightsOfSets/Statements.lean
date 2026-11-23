import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Points
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

def HeightLowerBound.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (A : HermLine n)
    (J : Type) [Fintype J] (s : J → IntegralSection P A.deg) (C : ℝ),
    (∀ j, (s j).SupNormLE A C) →
    (∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x) →
    ∀ x ∈ P.points (AlgebraicClosure ℚ), -C ≤ height A x

def HeightMetricChange.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (A A' : HermLine n),
    A.deg = A'.deg → ∀ B : ℝ,
    (∀ z ∈ P.points ℂ, |Real.log (A.metric z) - Real.log (A'.metric z)| ≤ B) →
    ∀ x ∈ P.points (AlgebraicClosure ℚ), |height A x - height A' x| ≤ B

def HeightLocalAgreement.Statement : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (n : ι → ℕ)
    (n' : ι' → ℕ) (A : HermLine n) (A' : HermLine n') (x : Cone n (AlgebraicClosure ℚ))
    (x' : Cone n' (AlgebraicClosure ℚ)), BlockNonzero x → BlockNonzero x' →
    ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L] (hx : ∀ k i, x k i ∈ L)
      (hx' : ∀ k i, x' k i ∈ L),
      (∀ v : FinitePlace L, finiteTerm A v (coordIn L x hx) = finiteTerm A' v (coordIn L x' hx')) →
      (∀ σ : L →+* ℂ, A.metric (fun k i ↦ σ (coordIn L x hx k i)) =
        A'.metric (fun k i ↦ σ (coordIn L x' hx' k i))) →
      height A x = height A' x'

def HeightPullback.Statement : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (n' : ι' → ℕ)
    (j : ι → ι') (hj : Function.Injective j) (A : HermLine (n' ∘ j))
    (x : Cone n' (AlgebraicClosure ℚ)), BlockNonzero x →
    height (A.pullback j hj) x = height A (HermLine.project j x)

def HeightComparison.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (A : HermLine n),
    ∃ (k : ℕ) (C : ℝ), ∀ x ∈ P.points (AlgebraicClosure ℚ),
      |height A x| ≤ k * height (HermLine.standard n) x + C

def DenseBoundedHeight.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n),
    ∃ (S : Set (Cone n (AlgebraicClosure ℚ))) (C : ℝ), S ⊆ P.points (AlgebraicClosure ℚ) ∧
      P.ZariskiDense S ∧ ∀ x ∈ S, height (HermLine.standard n) x ≤ C

def SlopeMaxExtension.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E' E E'' : HermitianBundle.{0} K),
    HermitianExtension E' E E'' → E.slopeMax ≤ max E'.slopeMax E''.slopeMax

def FlagDegreeBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ)
    (F : Fin (r + 1) → Submodule (𝓞 K) E.carrier), Monotone F → (∀ i, E.Saturated (F i)) →
    (∀ i, E.rank (F i) = i) →
    ∀ i, -((E.normDegree (F i) : ℝ) : EReal) ≥ -(((i : ℕ) : EReal) * E.slopeMax)

section Inhabitants

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in
theorem evalCone_chartMonomial {F : Type*} [CommRing F] (z : Cone n F)
    (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by
  simp [evalCone, chartMonomial, eval₂_prod]

theorem chartSection_supNormLE (P : ArithVariety n) (c0 : (k : ι) → Fin (n k + 1)) :
    (IntegralSection.chartSection P c0).SupNormLE (HermLine.standard n) 0 := by
  intro z hz c d e he hc
  have hpos : 0 < ∏ k, l2Norm (z k) := Finset.prod_pos fun k _ ↦ vectorL2Norm_pos (hz.1 k)
  have h0 : evalCone z (1 * e - chartMonomial c0 1 * chartMonomial c d) = 0 := hz.2 _ he.2
  simp only [evalCone, eval₂_sub, eval₂_mul, one_mul, sub_eq_zero] at h0
  have hm : evalCone z (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  have hmn : 0 < ‖evalCone z (chartMonomial c d)‖ := norm_pos_iff.mpr hm
  change ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * ∏ k, l2Norm (z k)) ≤ Real.exp 0
  have h1 : evalCone z e = evalCone z (chartMonomial c0 1) * evalCone z (chartMonomial c d) := by
    simp only [evalCone]; exact h0
  rw [h1, norm_mul, Real.exp_zero, div_le_one (mul_pos hmn hpos), mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hmn.le
  rw [evalCone_chartMonomial, norm_prod]
  refine Finset.prod_le_prod (fun k _ ↦ norm_nonneg _) (fun k _ ↦ ?_)
  simpa using norm_le_l2Norm (z k) (c0 k)

end Inhabitants

end

end GroundTheory.Heights₂.Heights
