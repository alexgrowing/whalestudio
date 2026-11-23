import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Formalism.REAL (Jm UJ inUJ hs muG Jm_mul_self Jm_conjTranspose)

noncomputable section

namespace GlobalTheory.LeviIso

def haarLoc (j : ℕ) : Measure (Fin j → Fin j → ℂ) :=
  (volume : Measure (Fin j → Fin j → ℂ)).withDensity
    fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)

instance (j : ℕ) : SigmaFinite (haarLoc j) := by
  unfold haarLoc
  infer_instance

instance sigmaFinite_ofReal_smul {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : ℝ) :
    SigmaFinite (ENNReal.ofReal c • μ) :=
  inferInstanceAs (SigmaFinite (c.toNNReal • μ))

def IsRadial {X : Type} [MeasurableSpace X] (μ : Measure X) (q : X → ℝ) (d : ℕ) : Prop :=
  Filter.Tendsto (fun r : ℝ => μ {x | Real.sqrt (q x) ≤ r} / ENNReal.ofReal (r ^ d))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))

variable {n n₀ a : ℕ} {j : Fin a → ℕ}

def SpansFlag (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ k y, y ∈ W k ↔ ∃ u : ∀ i, Fin (j i) → ℂ, (∀ i : Fin a, ¬ i.castSucc < k → u i = 0) ∧ y = ∑ i, B i *ᵥ u i

def IsFrame (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (B₀ : Matrix (Fin n) (Fin n₀) ℂ) : Prop :=
  (∀ i, (B i)ᴴ * B i = 1) ∧ (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) ∧ (∀ i k, (B i)ᴴ * Jm ε * B k = 0) ∧
    (∀ i, (B i)ᴴ * B₀ = 0) ∧ B₀ᴴ * B₀ = 1 ∧ Jm ε * B₀ = B₀ * Jm ε₀ ∧
    ∑ i, B i * (B i)ᴴ + ∑ i, Jm ε * B i * (B i)ᴴ * Jm ε + B₀ * B₀ᴴ = 1

def lev (ε : Fin n → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ)
    (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Matrix (Fin n₀) (Fin n₀) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, B i * x i * (B i)ᴴ + ∑ i, Jm ε * B i * (x i)⁻¹ᴴ * (B i)ᴴ * Jm ε + B₀ * g * B₀ᴴ

variable {ε : Fin n → Bool} {ε₀ : Fin n₀ → Bool} {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ}
  {B₀ : Matrix (Fin n) (Fin n₀) ℂ}

theorem IsFrame.J_B₀ (h : IsFrame ε ε₀ B B₀) (i : Fin a) : (B i)ᴴ * Jm ε * B₀ = 0 := by
  rw [Matrix.mul_assoc, h.2.2.2.2.2.1, ← Matrix.mul_assoc, h.2.2.2.1 i, Matrix.zero_mul]

theorem IsFrame.B₀_B (h : IsFrame ε ε₀ B B₀) (i : Fin a) : B₀ᴴ * B i = 0 := by
  have e := congrArg Matrix.conjTranspose (h.2.2.2.1 i)
  simpa [Matrix.conjTranspose_mul] using e

theorem IsFrame.B₀_J (h : IsFrame ε ε₀ B B₀) (i : Fin a) : B₀ᴴ * Jm ε * B i = 0 := by
  have e := congrArg Matrix.conjTranspose (h.J_B₀ i)
  simpa [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc] using e

theorem IsFrame.sum_mul (h : IsFrame ε ε₀ B B₀) {m : Type} (y : ∀ i, Matrix m (Fin (j i)) ℂ) (i : Fin a) :
    (∑ k, y k * (B k)ᴴ) * B i = y i := by
  rw [Matrix.sum_mul, Finset.sum_eq_single i]
  · rw [Matrix.mul_assoc, h.1 i, Matrix.mul_one]
  · intro k _ hk
    rw [Matrix.mul_assoc, h.2.1 k i hk, Matrix.mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

variable (x x' : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g g' : Matrix (Fin n₀) (Fin n₀) ℂ)

theorem IsFrame.lev_mul_B (h : IsFrame ε ε₀ B B₀) (i : Fin a) : lev ε B B₀ x g * B i = B i * x i := by
  have eJ : ∀ k, (B k)ᴴ * (Jm ε * B i) = 0 := fun k => by
    rw [← Matrix.mul_assoc]
    exact h.2.2.1 k i
  have s1 : (∑ k, B k * x k * (B k)ᴴ) * B i = B i * x i := h.sum_mul (fun k => B k * x k) i
  have s2 : (∑ k, Jm ε * B k * (x k)⁻¹ᴴ * (B k)ᴴ * Jm ε) * B i = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by simp only [Matrix.mul_assoc, eJ, Matrix.mul_zero]
  have s3 : B₀ * g * B₀ᴴ * B i = 0 := by
    simp only [Matrix.mul_assoc, h.B₀_B i, Matrix.mul_zero]
  unfold lev
  rw [Matrix.add_mul, Matrix.add_mul, s1, s2, s3, add_zero, add_zero]

theorem IsFrame.lev_mul_JB (h : IsFrame ε ε₀ B B₀) (i : Fin a) :
    lev ε B B₀ x g * (Jm ε * B i) = Jm ε * B i * (x i)⁻¹ᴴ := by
  have hJJ : ∀ {m : Type} (M : Matrix (Fin n) m ℂ), Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have eJ : ∀ k, (B k)ᴴ * (Jm ε * B i) = 0 := fun k => by
    rw [← Matrix.mul_assoc]
    exact h.2.2.1 k i
  have e₀ : B₀ᴴ * (Jm ε * B i) = 0 := by
    rw [← Matrix.mul_assoc]
    exact h.B₀_J i
  have s1 : (∑ k, B k * x k * (B k)ᴴ) * (Jm ε * B i) = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by simp only [Matrix.mul_assoc, eJ, Matrix.mul_zero]
  have s2 : (∑ k, Jm ε * B k * (x k)⁻¹ᴴ * (B k)ᴴ * Jm ε) * (Jm ε * B i) = Jm ε * B i * (x i)⁻¹ᴴ := by
    rw [Matrix.sum_mul, Finset.sum_eq_single i]
    · simp only [Matrix.mul_assoc, hJJ, h.1 i, Matrix.mul_one]
    · intro k _ hk
      simp only [Matrix.mul_assoc, hJJ, h.2.1 k i hk, Matrix.mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have s3 : B₀ * g * B₀ᴴ * (Jm ε * B i) = 0 := by
    simp only [Matrix.mul_assoc, e₀, Matrix.mul_zero]
  unfold lev
  rw [Matrix.add_mul, Matrix.add_mul, s1, s2, s3, zero_add, add_zero]

theorem IsFrame.lev_mul_B₀ (h : IsFrame ε ε₀ B B₀) : lev ε B B₀ x g * B₀ = B₀ * g := by
  have eJ : ∀ k, (B k)ᴴ * (Jm ε * B₀) = 0 := fun k => by
    rw [← Matrix.mul_assoc]
    exact h.J_B₀ k
  have s1 : (∑ k, B k * x k * (B k)ᴴ) * B₀ = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by
      simp only [Matrix.mul_assoc, h.2.2.2.1 k, Matrix.mul_zero]
  have s2 : (∑ k, Jm ε * B k * (x k)⁻¹ᴴ * (B k)ᴴ * Jm ε) * B₀ = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by simp only [Matrix.mul_assoc, eJ, Matrix.mul_zero]
  have s3 : B₀ * g * B₀ᴴ * B₀ = B₀ * g := by
    simp only [Matrix.mul_assoc, h.2.2.2.2.1, Matrix.mul_one]
  unfold lev
  rw [Matrix.add_mul, Matrix.add_mul, s1, s2, s3, zero_add, zero_add]

theorem IsFrame.ext (h : IsFrame ε ε₀ B B₀) {m : Type} {M N : Matrix m (Fin n) ℂ} (h1 : ∀ i, M * B i = N * B i)
    (h2 : ∀ i, M * (Jm ε * B i) = N * (Jm ε * B i)) (h3 : M * B₀ = N * B₀) : M = N := by
  have h2' : ∀ i, M * Jm ε * B i = N * Jm ε * B i := fun i => by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h2 i]
  calc M = M * (1 : Matrix (Fin n) (Fin n) ℂ) := (Matrix.mul_one M).symm
    _ = N * (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← h.2.2.2.2.2.2]
      simp only [Matrix.mul_add, Matrix.mul_sum, ← Matrix.mul_assoc, h1, h2', h3]
    _ = N := Matrix.mul_one N

theorem IsFrame.lev_one (h : IsFrame ε ε₀ B B₀) : lev ε B B₀ (fun _ => 1) 1 = 1 := by
  unfold lev
  simp only [inv_one, Matrix.conjTranspose_one, Matrix.mul_one]
  exact h.2.2.2.2.2.2

theorem IsFrame.lev_mul (h : IsFrame ε ε₀ B B₀) :
    lev ε B B₀ (fun i => x i * x' i) (g * g') = lev ε B B₀ x g * lev ε B B₀ x' g' := by
  refine h.ext (fun i => ?_) (fun i => ?_) ?_
  · rw [Matrix.mul_assoc (lev ε B B₀ x g), h.lev_mul_B x' g', ← Matrix.mul_assoc (lev ε B B₀ x g),
      h.lev_mul_B x g, h.lev_mul_B, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc (lev ε B B₀ x g), h.lev_mul_JB x' g', ← Matrix.mul_assoc (lev ε B B₀ x g),
      h.lev_mul_JB x g, h.lev_mul_JB]
    simp only [Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc (lev ε B B₀ x g), h.lev_mul_B₀ x' g', ← Matrix.mul_assoc (lev ε B B₀ x g),
      h.lev_mul_B₀ x g, h.lev_mul_B₀, Matrix.mul_assoc]

theorem lev_conjTranspose : (lev ε B B₀ x g)ᴴ = lev ε B B₀ (fun i => (x i)ᴴ) gᴴ := by
  unfold lev
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, Matrix.conjTranspose_nonsing_inv,
    Matrix.mul_assoc]

theorem IsFrame.inUJ_lev (h : IsFrame ε ε₀ B B₀) (hx : ∀ i, (x i).det ≠ 0) (hg : inUJ ε₀ g) :
    inUJ ε (lev ε B B₀ x g) := by
  have hl : ∀ i, (x i)⁻¹ * x i = 1 := fun i => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hx i))
  have hr : ∀ i, (x i)ᴴ * ((x i)ᴴ)⁻¹ = 1 := fun i => by
    rw [← Matrix.conjTranspose_nonsing_inv, ← Matrix.conjTranspose_mul, hl i, Matrix.conjTranspose_one]
  have hJJ : ∀ {m : Type} (M : Matrix (Fin n) m ℂ), Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have hJ₀ : ∀ {m : Type} (M : Matrix (Fin n₀) m ℂ), Jm ε * (B₀ * M) = B₀ * (Jm ε₀ * M) := fun M => by
    rw [← Matrix.mul_assoc, h.2.2.2.2.2.1, Matrix.mul_assoc]
  have hg' : gᴴ * (Jm ε₀ * g) = Jm ε₀ := by
    rw [← Matrix.mul_assoc]
    exact hg
  have eB : ∀ (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (k : Matrix (Fin n₀) (Fin n₀) ℂ) (i : Fin a)
      {m : Type} (M : Matrix (Fin (j i)) m ℂ), lev ε B B₀ y k * (B i * M) = B i * (y i * M) :=
    fun y k i {_} M => by rw [← Matrix.mul_assoc, h.lev_mul_B, Matrix.mul_assoc]
  have eJB : ∀ (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (k : Matrix (Fin n₀) (Fin n₀) ℂ) (i : Fin a)
      {m : Type} (M : Matrix (Fin (j i)) m ℂ),
      lev ε B B₀ y k * (Jm ε * (B i * M)) = Jm ε * (B i * ((y i)⁻¹ᴴ * M)) :=
    fun y k i {_} M => by
      rw [← Matrix.mul_assoc (Jm ε), ← Matrix.mul_assoc, h.lev_mul_JB]
      simp only [Matrix.mul_assoc]
  have eB₀ : ∀ (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (k : Matrix (Fin n₀) (Fin n₀) ℂ)
      {m : Type} (M : Matrix (Fin n₀) m ℂ), lev ε B B₀ y k * (B₀ * M) = B₀ * (k * M) :=
    fun y k {_} M => by rw [← Matrix.mul_assoc, h.lev_mul_B₀, Matrix.mul_assoc]
  show (lev ε B B₀ x g)ᴴ * Jm ε * lev ε B B₀ x g = Jm ε
  rw [lev_conjTranspose]
  refine h.ext (fun i => ?_) (fun i => ?_) ?_
  · simp only [Matrix.mul_assoc, h.lev_mul_B, eJB, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_conjTranspose, hl, Matrix.mul_one]
  · simp only [Matrix.mul_assoc, h.lev_mul_JB, hJJ, eB, Matrix.conjTranspose_nonsing_inv, hr,
      Matrix.mul_one]
  · simp only [Matrix.mul_assoc, h.lev_mul_B₀, hJ₀, eB₀, hg', h.2.2.2.2.2.1]

theorem IsFrame.lev_inj (h : IsFrame ε ε₀ B B₀) (e : lev ε B B₀ x g = lev ε B B₀ x' g') : x = x' ∧ g = g' := by
  have hB : ∀ i, B i * x i = B i * x' i := fun i => by
    rw [← h.lev_mul_B x g i, e, h.lev_mul_B]
  have hB₀ : B₀ * g = B₀ * g' := by
    rw [← h.lev_mul_B₀ x g, e, h.lev_mul_B₀]
  refine ⟨funext fun i => ?_, ?_⟩
  · have e' := congrArg ((B i)ᴴ * ·) (hB i)
    simpa [← Matrix.mul_assoc, h.1 i] using e'
  · have e' := congrArg (B₀ᴴ * ·) hB₀
    simpa [← Matrix.mul_assoc, h.2.2.2.2.1] using e'

def IsLeviChart (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (τ τ₀ : ℂ →+* ℂ)
    (θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε) : Prop :=
  Measurable θ ∧
  (∀ m, m ∈ flagM ε W ↔ ∃ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) ∧ θ z = m) ∧
  (∀ z z' : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
    (∀ i, (Matrix.of (z'.1 i)).det ≠ 0) →
    θ z * θ z' = θ (fun i r s => (Matrix.of (z.1 i) * Matrix.of (z'.1 i)) r s, z.2 * z'.2) ∧
      (θ z = θ z' → z = z')) ∧
  (∀ z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
    (∀ i, locSize j W (uMat (θ z)) i = ‖(Matrix.of (z.1 i)).det‖ ^ (-(1 : ℝ) / j i)) ∧
    ∀ g : UJ ε, (∀ i, uMat g * A i = A i * (Matrix.of (z.1 i)).map τ) → uMat g * A₀ = A₀ * (uMat z.2).map τ₀ →
      g * (θ z)⁻¹ ∈ flagN ε W) ∧
  ∀ (μ : Measure (UJ ε)) (c : ℝ), IsGaugeSub (flagM ε W) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) μ → IsGauge ε₀ c →
    μ = ((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod
      (ENNReal.ofReal c • muG ε₀)).map θ

end GlobalTheory.LeviIso
