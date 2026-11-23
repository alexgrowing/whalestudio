import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtEqComp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem der_nU {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) {Ψ Ψ' : ℝ → S4 F}
    (h : Der Ψ Ψ') (b : A F) :
    Der (fun s => W.Om (nU b) (Ψ s)) (fun s => W.Om (nU b) (Ψ' s)) := by
  intro t v
  simp only [W.Om_n]
  exact (h t v).const_mul _

private theorem integrable_mul_char {F : Type} [Field F] [NumberField F] (φ : S4 F)
    {c : V4 F → ℂ} (hc : Continuous c) (hn : ∀ y, ‖c y‖ = 1) :
    Integrable (fun y => φ.1 y * c y) (adeleMeasurePi F) := by
  obtain ⟨N, hN⟩ := wtInt F
  obtain ⟨hφ, K, hK, hB⟩ := wtBound F φ
  obtain ⟨B, hB⟩ := hB N
  refine Integrable.mono' ((hN K hK).const_mul B) (hφ.mul hc).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, hn, mul_one]
  exact hB () (Set.mem_univ _) y

private theorem der_wW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) {Ψ Ψ' : ℝ → S4 F}
    (h : Der Ψ Ψ') (hd : ∀ t, Dom (Metric.ball t 1) fun s => (Ψ' s).1) :
    Der (fun s => W.Om (wW F) (Ψ s)) (fun s => W.Om (wW F) (Ψ' s)) := by
  intro t v
  simp only [W.Om_w, ft4]
  obtain ⟨N, hN⟩ := wtInt F
  obtain ⟨K, hK, hB⟩ := hd t
  obtain ⟨B, hB⟩ := hB N
  have e : ∀ i, Continuous fun y : V4 F => y i := fun i => continuous_apply i
  have cB : Continuous fun y : V4 F => B4 D.δ y v :=
    ((continuous_const.mul (((e 2).mul continuous_const).sub
      (continuous_const.mul ((e 3).mul continuous_const)))).sub
      ((e 1).mul continuous_const)).sub ((e 0).mul continuous_const)
  have cψ : Continuous fun y : V4 F => ψ (B4 D.δ y v) := continuous_ψ.comp cB
  have cont : ∀ φ : S4 F, Continuous fun y => φ.1 y * ψ (B4 D.δ y v) :=
    fun φ => (wtBound F φ).1.mul cψ
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => (Ψ s).1 y * ψ (B4 D.δ y v)) (F' := fun s y => (Ψ' s).1 y * ψ (B4 D.δ y v))
    (bound := fun y => B * wt K N y) (μ := adeleMeasurePi F)
    (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun s => (cont (Ψ s)).aestronglyMeasurable)
    (integrable_mul_char (Ψ t) cψ fun y => norm_ψ _)
    (cont (Ψ' t)).aestronglyMeasurable
    (Eventually.of_forall fun y s hs => by
      rw [norm_mul, norm_ψ, mul_one]
      exact hB s hs y)
    ((hN K hK).const_mul B)
    (Eventually.of_forall fun y s _ => (h s y).mul_const _)).2

theorem UpperTheory.ConvolutionTheory.R2.Ff.omDer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), OmDer W := by
  intro F E _ _ _ _ _ _ _ D W Ψ Ψ' h hd g
  have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
    rw [(gen F).1]
    trivial
  have wstep : ∀ y, Der (fun s => W.Om y (Ψ s)) (fun s => W.Om y (Ψ' s)) →
      Der (fun s => W.Om (wW F * y) (Ψ s)) (fun s => W.Om (wW F * y) (Ψ' s)) := by
    intro y hy
    simp only [map_mul, Module.End.mul_apply]
    exact der_wW W hy (hd y)
  induction hg using Subgroup.closure_induction_left with
  | one => simpa using h
  | mul_left x hx y _ ih =>
    rcases hx with ⟨b, rfl⟩ | hx
    · simp only [map_mul, Module.End.mul_apply]
      exact der_nU W ih b
    · rw [Set.mem_singleton_iff.1 hx]
      exact wstep y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with ⟨b, rfl⟩ | hx
    · rw [← nU_neg]
      simp only [map_mul, Module.End.mul_apply]
      exact der_nU W ih (-b)
    · rw [Set.mem_singleton_iff.1 hx, wW_inv, ← wW_mul_wW, mul_assoc, mul_assoc]
      exact wstep _ (wstep _ (wstep y ih))
