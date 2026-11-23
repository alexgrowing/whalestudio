import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceRate
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergySum
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Telescoping
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens chartPartMeasure
  existsPartition)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

section Objects

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def Family.coefWeight (F : Family A) (x : Option (Fin F.m) → ℝ) (t : ℝ) : X → ℝ :=
  fun p => ∑ i, x (some i) * (F.sys i).ph t p

def Family.coefForm (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t : ℝ) : LocPot X :=
  F.chernForm (fun i => x (some i)) t + LocPot.rsmul (x none) a

def Family.coefRefForm (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) : LocPot X :=
  lincomb F.m (fun i => x (some i)) (fun i => (F.R i).θ) + LocPot.rsmul (x none) a

def Family.weightEnergy (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (D + 1), mInt A
    (fun i : Fin D => if (i : ℕ) < k then F.coefForm a x t else F.coefRefForm a x) (F.coefWeight x t)

def Family.arithSelfInt (F : Family A) (a : LocPot X) (a₀ : MvPolynomial (Option (Fin F.m)) ℝ)
    (δ : ℝ) (x : Option (Fin F.m) → ℝ) (t : ℝ) : ℝ :=
  (MvPolynomial.eval x a₀ + F.weightEnergy a x t) / δ

def Family.mixedProduct (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t t' : ℝ)
    (k : ℕ) : Fin D → LocPot X :=
  fun i => if (i : ℕ) < k then F.coefForm a x t else F.coefForm a x t'

def Family.Admissible (F : Family A) (t : ℝ) : Prop :=
  0 < t ∧ ∀ i, (F.sys i).ell₀ ≤ ell t

end Objects

section Potentials

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem isPotential_lincomb : ∀ (m : ℕ) (c : Fin m → ℝ) (P : Fin m → LocPot X),
    (∀ i, IsPotential A (P i)) → IsPotential A (lincomb m c P)
  | 0, _, _, _ => ReciprocityTheory.AnForm.M.isPotential_ofFun A _ fun _ => contDiffOn_const
  | m + 1, c, P, hP => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _
      (ReciprocityTheory.AnForm.M.isPotentialRsmul A (c 0) (P 0) (hP 0))
      (isPotential_lincomb m _ _ fun i => hP i.succ)

theorem Family.coefForm_isPotential (F : Family A) {a : LocPot X} (ha : IsPotential A a)
    (x : Option (Fin F.m) → ℝ) {t : ℝ} (ht : F.Admissible t) : IsPotential A (F.coefForm a x t) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd A _ _
    (isPotential_lincomb _ _ _ fun i => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (F.R i).θ_pot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ ((F.sys i).smooth t ht.1 (ht.2 i))))
    (ReciprocityTheory.AnForm.M.isPotentialRsmul A _ a ha)

theorem Family.mixedProduct_isPotential (F : Family A) {a : LocPot X} (ha : IsPotential A a)
    (x : Option (Fin F.m) → ℝ) {t t' : ℝ} (ht : F.Admissible t) (ht' : F.Admissible t') (k : ℕ)
    (i : Fin D) : IsPotential A (F.mixedProduct a x t t' k i) := by
  unfold Family.mixedProduct
  split_ifs
  · exact F.coefForm_isPotential ha x ht
  · exact F.coefForm_isPotential ha x ht'

end Potentials

def Convergence.TVHyp {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {A : FinHolAtlas D X} (F : Family A) (a : LocPot X)
    (Λ M CE L₀ : ℝ) : Prop :=
  ∀ x : Option (Fin F.m) → ℝ, ∑ o, |x o| ≤ Λ → ∀ t t' : ℝ, 0 < t' → t' ≤ t → L₀ ≤ ell t →
    ∀ k ≤ D, TVBounds A (F.mixedProduct a x t t' k) F.Yo F.r M CE

def WeightCocycle.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (F : Family A) (a : LocPot X), IsPotential A a → ∀ (x : Option (Fin F.m) → ℝ) (t t' : ℝ),
    F.Admissible t → F.Admissible t' →
      F.weightEnergy a x t - F.weightEnergy a x t' =
        ∑ k ∈ Finset.range (D + 1),
          mInt A (F.mixedProduct a x t t' k) fun p => F.coefWeight x t p - F.coefWeight x t' p

def PolynomialInWeights.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (F : Family A) (a : LocPot X), IsPotential A a → ∀ t : ℝ, F.Admissible t →
      ∃ p : MvPolynomial (Option (Fin F.m)) ℝ, p.totalDegree ≤ D + 1 ∧
        ∀ x, MvPolynomial.eval x p = F.weightEnergy a x t

def Convergence.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (D : ℕ) (A : FinHolAtlas D X) (F : Family A) (a : LocPot X)
    (a₀ : MvPolynomial (Option (Fin F.m)) ℝ) (δ Λ M CE L₀ : ℝ),
    IsPotential A a → 0 < δ → (∀ i, (F.sys i).ell₀ ≤ L₀) → 0 ≤ M → 0 ≤ CE →
    Convergence.TVHyp F a Λ M CE L₀ →
    ∃ C L₁ : ℝ, ∀ x : Option (Fin F.m) → ℝ, ∑ o, |x o| ≤ Λ → ∀ t t' : ℝ, 0 < t' → t' ≤ t →
      L₁ ≤ ell t → |F.arithSelfInt a a₀ δ x t - F.arithSelfInt a a₀ δ x t'| ≤ convRate D C t

def CoefficientLimit.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (D : ℕ) (A : FinHolAtlas D X) (F : Family A) (a : LocPot X)
    (a₀ : MvPolynomial (Option (Fin F.m)) ℝ) (δ L₀ : ℝ),
    IsPotential A a → a₀.totalDegree ≤ D + 1 → 0 < δ → (∀ i, (F.sys i).ell₀ ≤ L₀) →
    (∀ Λ : ℝ, ∃ M CE : ℝ, 0 ≤ M ∧ 0 ≤ CE ∧ Convergence.TVHyp F a Λ M CE L₀) →
    ∃ P : MvPolynomial (Option (Fin F.m)) ℝ, P.totalDegree ≤ D + 1 ∧
      (∀ x, Tendsto (fun t => F.arithSelfInt a a₀ δ x t) (𝓝[>] 0) (𝓝 (MvPolynomial.eval x P))) ∧
      ∀ p : ℝ → MvPolynomial (Option (Fin F.m)) ℝ,
        (∀ᶠ t in 𝓝[>] 0, (p t).totalDegree ≤ D + 1 ∧
          ∀ x, MvPolynomial.eval x (p t) = F.arithSelfInt a a₀ δ x t) →
        ∀ α, Tendsto (fun t => (p t).coeff α) (𝓝[>] 0) (𝓝 (P.coeff α))

section Inhabitants

open ReciprocityTheory.AnForm (fsDens levi maDens_one fsDens_pos)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineCharts projLineCharts_potential_zero isPsh_const)

attribute [local instance] projectiveLineBorel projectiveLine_borelSpace

def projectiveLineDataEmptyDivisor : RegChartData p1 where
  toRegCharts := projLineCharts
  Yo := Set.univ
  isOpen_Yo := isOpen_univ
  S _ := ∅
  mem_Yo_iff _ z _ := by simp [ReciprocityTheory.AnForm.A.coordDiv]
  r _ := Real.exp 1
  f _ _ := 0
  f_cont _ := continuousOn_const
  f_bdd _ := ⟨0, fun _ _ => by simp⟩
  r_chart _ _ _ := by simp
  one_le_r _ _ := Real.one_le_exp zero_le_one
  φ _ := 0
  φ_smooth _ := contDiffOn_const
  psh j := by
    show ReciprocityTheory.AnForm.A.IsPsh _ (projLineCharts.u (fun _ => 0) j)
    rw [projLineCharts_potential_zero]
    exact isPsh_const _ 0
  C := 0
  φ_le _ _ := le_rfl
  le_φ _ _ := by simp
  grad j z _ := by
    show ‖fderiv ℝ (projLineCharts.u (fun _ => 0) j) z‖ ≤ _
    rw [projLineCharts_potential_zero]
    simp

def projectiveLineSystemEmptyDivisor : System projectiveLineDataEmptyDivisor where
  ph _ _ := 0
  C := 0
  ell₀ := 1
  smooth _ _ _ _ := contDiffOn_const
  le_ph _ _ _ _ _ := le_rfl
  ph_le _ _ _ _ := le_rfl
  le_log _ _ _ _ := by simp
  thGe t _ _ := by
    intro x k y _ w
    have h : ((fun z => projectiveLineDataEmptyDivisor.θ.φ x z + (fun _ : OnePoint ℂ => (0 : ℝ)) z) ∘ (p1.chart k).symm) =
        fun _ => (0 : ℝ) := by
      funext z
      show (0 : ℝ) + 0 = 0
      simp
    rw [h, levi_const, errE_zero]
    simp
  near t ht _ _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  far t ht _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t * _
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  mono _ _ _ _ _ _ := by simp
  c2 _ _ _ _ := ⟨tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _,
    tendstoUniformlyOn_self _ _ _⟩

def projectiveLineFamilyEmptyDivisor : Family p1 where
  m := 1
  R _ := projectiveLineDataEmptyDivisor
  sys _ := projectiveLineSystemEmptyDivisor
  Yo := Set.univ
  r _ := Real.exp 1
  om := fsPot
  Yo_eq _ := rfl
  r_eq _ _ _ := rfl
  om_eq _ := rfl

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
