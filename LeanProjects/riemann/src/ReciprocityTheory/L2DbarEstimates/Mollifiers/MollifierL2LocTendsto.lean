import Mathlib

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

structure Kernel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (μ : Measure E) where
  toFun : E → ℝ
  r : ℝ
  r_pos : 0 < r
  smooth : ContDiff ℝ ∞ toFun
  nonneg : ∀ x, 0 ≤ toFun x
  support_subset : Function.support toFun ⊆ ball (0 : E) r
  integral_eq_one : ∫ x, toFun x ∂μ = 1

noncomputable def moll {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {μ : Measure E} (K : Kernel E μ) (u : E → ℂ) : E → ℂ :=
  K.toFun ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u

noncomputable def Dop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (c : Fin m → ℂ) (v : Fin m → E) (g : Fin m → E → ℂ) (x : E) : ℂ :=
  ∑ k, c k * fderiv ℝ (g k) x (v k)

def IsWeakD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (μ : Measure E) {m : ℕ} (c : Fin m → ℂ) (v : Fin m → E) (g : Fin m → E → ℂ) (w : E → ℂ) :
    Prop :=
  (∀ k, LocallyIntegrable (g k) μ) ∧ LocallyIntegrable w μ ∧
    ∀ φ : E → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, w x * φ x ∂μ = - ∑ k, c k * ∫ x, g k x * fderiv ℝ φ x (v k) ∂μ

noncomputable def Kernel.ofBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (φ : ContDiffBump (0 : E)) : Kernel E μ where
  toFun := φ.normed μ
  r := φ.rOut
  r_pos := φ.rOut_pos
  smooth := φ.contDiff_normed
  nonneg := φ.nonneg_normed
  support_subset := (φ.support_normed_eq (μ := μ)).subset
  integral_eq_one := φ.integral_normed

noncomputable def stdBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (ε : ℝ) : ContDiffBump (0 : E) where
  rIn := (if 0 < ε then ε else 1) / 2
  rOut := if 0 < ε then ε else 1
  rIn_pos := by split_ifs with h <;> linarith
  rIn_lt_rOut := by split_ifs with h <;> linarith

noncomputable def Kernel.std (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ε : ℝ) : Kernel E μ :=
  Kernel.ofBump E μ (stdBump E ε)

def SmoothSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (K : Kernel E μ) (u : E → ℂ), LocallyIntegrable u μ → ContDiff ℝ ∞ (moll K u)

def SupportSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (K : Kernel E μ) (u : E → ℂ), Function.support (moll K u) ⊆ Function.support u + ball 0 K.r

def CompactSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (K : Kernel E μ) (u : E → ℂ), HasCompactSupport u → HasCompactSupport (moll K u)

def CongrSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (K : Kernel E μ) (u u' : E → ℂ), u =ᵐ[μ] u' → moll K u = moll K u'

def LocalSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (K : Kernel E μ) (u : E → ℂ) (s : Set E) (x : E), ball x K.r ⊆ s →
    moll K (s.indicator u) x = moll K u x

def YoungSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (K : Kernel E μ) (u : E → ℂ) (s : Set E), MeasurableSet s → AEStronglyMeasurable u μ →
    eLpNorm (moll K u) 2 (μ.restrict s) ≤ eLpNorm u 2 (μ.restrict (thickening K.r s))

def MollifierMemL2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (K : Kernel E μ) (u : E → ℂ), MemLp u 2 μ →
    MemLp (moll K u) 2 μ ∧ eLpNorm (moll K u) 2 μ ≤ eLpNorm u 2 μ

def MollifierL2Tendsto (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : Prop :=
  ∀ (l : Filter ι) (K : ι → Kernel E μ), Tendsto (fun i => (K i).r) l (𝓝 0) →
    ∀ u : E → ℂ, MemLp u 2 μ → Tendsto (fun i => eLpNorm (moll (K i) u - u) 2 μ) l (𝓝 0)

def MollifierL2LocTendsto (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : Prop :=
  ∀ (l : Filter ι) (K : ι → Kernel E μ), Tendsto (fun i => (K i).r) l (𝓝 0) →
    ∀ u : E → ℂ, (∀ C, IsCompact C → MemLp u 2 (μ.restrict C)) →
      ∀ C, IsCompact C → Tendsto (fun i => eLpNorm (moll (K i) u - u) 2 (μ.restrict C)) l (𝓝 0)

def WeightedTendstoSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : Prop :=
  ∀ (l : Filter ι) (K : ι → Kernel E μ), Tendsto (fun i => (K i).r) l (𝓝 0) →
    ∀ u : E → ℂ, (∀ C, IsCompact C → MemLp u 2 (μ.restrict C)) →
      ∀ C, IsCompact C → ∀ w : E → ℝ, Continuous w →
        Tendsto (fun i => ∫⁻ x in C, ‖moll (K i) u x - u x‖ₑ ^ 2 * ENNReal.ofReal (w x) ∂μ) l
          (𝓝 0)

def WeakCommSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (v : Fin m → E) (g : Fin m → E → ℂ) (w : E → ℂ),
    IsWeakD μ c v g w → ∀ K : Kernel E μ, Dop c v (fun k => moll K (g k)) = moll K w

def SmoothWeakSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (v : Fin m → E) (g : Fin m → E → ℂ),
    (∀ k, ContDiff ℝ 1 (g k)) → IsWeakD μ c v g (Dop c v g)

def GraphSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : Prop :=
  ∀ (l : Filter ι) (K : ι → Kernel E μ), Tendsto (fun i => (K i).r) l (𝓝 0) →
    ∀ (m : ℕ) (c : Fin m → ℂ) (v : Fin m → E) (g : Fin m → E → ℂ) (w : E → ℂ),
      IsWeakD μ c v g w → (∀ k, MemLp (g k) 2 μ) → MemLp w 2 μ →
        (∀ k, Tendsto (fun i => eLpNorm (moll (K i) (g k) - g k) 2 μ) l (𝓝 0)) ∧
        Tendsto (fun i => eLpNorm (Dop c v (fun k => moll (K i) (g k)) - w) 2 μ) l (𝓝 0)

def StdSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : Prop :=
  Tendsto (fun ε : ℝ => (Kernel.std E μ ε).r) (𝓝[>] 0) (𝓝 0)

noncomputable example (n : ℕ) : Kernel (EuclideanSpace ℂ (Fin n)) volume :=
  Kernel.std (EuclideanSpace ℂ (Fin n)) volume 1

theorem isWeakD_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ) (c : Fin m → ℂ) (v : Fin m → E) :
    IsWeakD μ c v (fun _ => 0) 0 := by
  refine ⟨fun _ => locallyIntegrable_zero, locallyIntegrable_zero, fun φ _ _ => ?_⟩
  simp

end ReciprocityTheory.L2DbarEstimates.B
