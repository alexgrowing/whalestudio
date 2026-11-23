import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTruncatedGaussiansWithDensitiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Filter Topology

namespace GlobalTheory.GaussMean.Limit

theorem tendsto_tsum_of_monotone {ι : Type*} (f : ℕ → ι → ENNReal) (g : ι → ENNReal)
    (hm : ∀ y, Monotone fun k => f k y) (ht : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    Tendsto (fun k => ∑' y, f k y) atTop (𝓝 (∑' y, g y)) := by
  letI : MeasurableSpace ι := ⊤
  have h := lintegral_tendsto_of_tendsto_of_monotone (μ := (Measure.count : Measure ι)) (f := f) (F := g)
    (fun k => (measurable_from_top).aemeasurable) (ae_of_all _ hm) (ae_of_all _ ht)
  simpa only [lintegral_count] using h

theorem tendsto_lintegral_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι] (μ : Measure α)
    (p : ι → α → Prop) (hp : ∀ y, MeasurableSet {x | p y x}) (f : ℕ → ι → α → ENNReal) (g : ι → α → ENNReal)
    (hf : ∀ k y, Measurable (f k y)) (hm : ∀ y x, Monotone fun k => f k y x)
    (ht : ∀ y x, Tendsto (fun k => f k y x) atTop (𝓝 (g y x))) :
    Tendsto (fun k => ∫⁻ x, (∑' y : {y // p y x}, f k y.1 x) ∂μ) atTop
      (𝓝 (∫⁻ x, (∑' y : {y // p y x}, g y.1 x) ∂μ)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone (fun k => Measurable.aemeasurable ?_)
    (ae_of_all _ fun x a b hab => ENNReal.tsum_le_tsum fun y => hm y.1 x hab)
    (ae_of_all _ fun x => tendsto_tsum_of_monotone (fun k (y : {y // p y x}) => f k y.1 x) _
      (fun y => hm y.1 x) fun y => ht y.1 x)
  have e : (fun x => ∑' y : {y // p y x}, f k y.1 x) = fun x => ∑' y, {x | p y x}.indicator (f k y) x := by
    funext x
    exact (tsum_subtype {y | p y x} fun y => f k y x).trans (tsum_congr fun y => rfl)
  rw [e]
  exact Measurable.ennreal_tsum fun y => (hf k y).indicator (hp y)

theorem measurable_coord (I : AutInst) (v : InfinitePlace I.F) (w : Fin I.n → ℂ) :
    Measurable fun x : I.GA => ((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ w := by
  have h0 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
    have e : (fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹) = fun g => uMat g⁻¹ := by
      funext g
      exact (Matrix.coe_units_inv g.1).symm
    rw [e]
    exact h0.comp continuous_inv
  have h2 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => ((uMat g)⁻¹ * (I.P v)⁻¹) *ᵥ w :=
    (h1.matrix_mul continuous_const).matrix_mulVec continuous_const
  exact h2.measurable.comp ((measurable_pi_apply v).comp measurable_fst)

theorem siegelMean_of_cc : SiegelMeanCc → SiegelMean := by
  intro H I hn s μf _ _ fund hfund
  obtain ⟨hfin, hH⟩ := H I hn s μf fund hfund
  refine ⟨hfin, ?_⟩
  choose φ D h1 h2 h3 using fun v => GlobalTheory.T.exists_truncated_gaussians_with_densities I.n (I.ε v)
  haveI := countable_V I
  have hs : sgn ℝ s ≠ 0 := by cases s <;> simp [sgn]
  have hL := tendsto_lintegral_tsum ((I.muA μf).restrict fund)
    (fun (y : Fin I.n → I.E) (x : I.GA) => y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s)
    (fun y => mand (measurableSet_mem_lam I y) (MeasurableSet.const _))
    (fun k y x => ENNReal.ofReal (∏ v, φ v k (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun y x => ENNReal.ofReal (∏ v, gauss (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun k y => ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun v _ =>
      (h1 v k).1.continuous.measurable.comp (measurable_coord I v _)))
    (fun y x a b hab => ENNReal.ofReal_le_ofReal
      (Finset.prod_le_prod (fun v _ => (h1 v a).2.2.1 _) fun v _ => (h2 v _).1 hab))
    (fun y x => ENNReal.tendsto_ofReal (tendsto_finset_prod _ fun v _ => (h2 v _).2))
  have hR : Tendsto (fun k => I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, D v k (sgn ℝ s))) atTop
      (𝓝 (I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, gaussDens (I.ε v) (sgn ℝ s)))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal ((tendsto_finset_prod _ fun v _ => h3 v _ hs).const_mul _)) (Or.inr hfin.ne)
  exact tendsto_nhds_unique hL (hR.congr fun k => (hH (fun v => φ v k) (fun v => D v k) fun v => h1 v k).symm)

end GlobalTheory.GaussMean.Limit
