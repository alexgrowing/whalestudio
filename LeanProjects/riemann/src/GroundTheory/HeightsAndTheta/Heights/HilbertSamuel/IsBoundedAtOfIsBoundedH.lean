import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsBoundedAt (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (c : ℝ) (s : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι),
    IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + τ * A.a k) →
    aeval y g = s * aeval y h →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ

def secNormAt (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ IsBoundedAt y A τ c s z}

def sectionL2Norm (μ : Measure ((Σ k, ι k) → ℂ)) (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (s : Ω) : ℝ :=
  Real.sqrt (∫ z, secNormAt y A τ s z ^ 2 ∂μ)

def IsZariskiDenseMeasure (P : Ideal (MRing ι)) (μ : Measure ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ (d : K → ℕ) (f : MRingOver ℂ ι), IsMultiHomog f d → (∀ᵐ z ∂μ, eval z f = 0) →
    ∀ z ∈ mcPts P, eval z f = 0

theorem isBoundedAt_of_isBoundedH {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {c : ℝ}
    {s : Ω} (hs : IsBoundedH P y A τ c s) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : IsBoundedAt y A τ c s z :=
  fun dg dh g h hg hh hd he => hs dg dh g h z hg hh hd he hz

theorem secNormAt_le {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {c : ℝ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hc : 0 ≤ c) (hs : IsBoundedAt y A τ c s z) : secNormAt y A τ s z ≤ c :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hc, hs⟩

theorem secNormAt_nonneg (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) :
    0 ≤ secNormAt y A τ s z := by
  rcases Set.eq_empty_or_nonempty {c : ℝ | 0 ≤ c ∧ IsBoundedAt y A τ c s z} with h | h
  · simp [secNormAt, h]
  · exact le_csInf h fun _ hx => hx.1

end Objects

def SectionL2Lattice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    ∀ μ : Measure ((Σ k, ι k) → ℂ), IsProbabilityMeasure μ → μ (mcPts (mCoordIdeal y))ᶜ = 0 →
      IsZariskiDenseMeasure (mCoordIdeal y) μ →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        IsSmallH (mCoordIdeal y) y A k (t : Ω) → (st : Ω) = s * t → ‖φ (n + k) st‖ ≤ ‖φ n s‖) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∀ (n : ℕ) (s : chartLat y A.a n), ‖φ n s‖ = sectionL2Norm μ y A n (s : Ω)

def natPtsMeasure : Measure ℂ :=
  Measure.sum fun j : ℕ => ((2 : ENNReal)⁻¹ ^ (j + 1)) • Measure.dirac ((j : ℂ) + 1)

def gridMeasure (J : Type) [Fintype J] : Measure (J → ℂ) :=
  Measure.pi fun _ => natPtsMeasure

theorem natPtsMeasure_univ : natPtsMeasure Set.univ = 1 := by
  rw [natPtsMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [show (fun j : ℕ => (2 : ENNReal)⁻¹ ^ (j + 1)) = fun j => 2⁻¹ * (2⁻¹) ^ j by
    funext j; rw [pow_succ, mul_comm]]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance : IsProbabilityMeasure natPtsMeasure := ⟨natPtsMeasure_univ⟩

instance (J : Type) [Fintype J] : IsProbabilityMeasure (gridMeasure J) := by
  unfold gridMeasure; infer_instance

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
