import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.MeasMul
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.UnfL

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem enorm_tsum_le' {β : Type*} (f : β → ℂ) : ‖∑' b, f b‖ₑ ≤ ∑' b, ‖f b‖ₑ := by
  by_cases h : ∑' b, ‖f b‖ₑ = ⊤
  · simp [h]
  · have hs : Summable fun b => ‖f b‖ := by
      simpa [toReal_enorm] using ENNReal.summable_toReal h
    have h1 : ‖∑' b, f b‖ ≤ ∑' b, ‖f b‖ := norm_tsum_le_tsum_norm hs
    have h2 : ENNReal.ofReal (∑' b, ‖f b‖) = ∑' b, ‖f b‖ₑ := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
      simp [ofReal_norm_eq_enorm]
    rw [← h2, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal h1

private theorem tsum_comm_of_enorm {α β : Type*} (f : α → β → ℂ) (h : ∑' a, ∑' b, ‖f a b‖ₑ ≠ ⊤) :
    ∑' b, ∑' a, f a b = ∑' a, ∑' b, f a b := by
  have h' : ∑' p : α × β, ‖Function.uncurry f p‖ₑ ≠ ⊤ := by
    have : ∑' p : α × β, ‖Function.uncurry f p‖ₑ = ∑' a, ∑' b, ‖f a b‖ₑ :=
      ENNReal.tsum_prod (f := fun a b => ‖f a b‖ₑ)
    rwa [this]
  have hs : Summable fun p => ‖Function.uncurry f p‖ := by
    simpa [toReal_enorm] using ENNReal.summable_toReal h'
  exact (Summable.of_norm hs).tsum_comm

theorem UpperTheory.ConvolutionTheory.R2.G.unfoldSum :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (σ : Rw F → Matrix.SpecialLinearGroup (Fin 2) F), _root_.UpperTheory.ConvolutionTheory.R2.M.RowSec σ → ∀ (ι : Type) [Countable ι] (u : ι → G1 F → ℂ), (∀ i, NInv (u i)) → ∑' i, abelian₂ M (u i) ≠ ⊤ →
    Summable (fun i => ‖M.I0 (av (u i))‖) ∧ IntegrableOn (fun g => ∑' r, ∑' i, u i (ratS F (σ r) * g)) M.D M.μ ∧
    ∫ g in M.D, ∑' r, ∑' i, u i (ratS F (σ r) * g) ∂M.μ = ∑' i, M.I0 (av (u i)) := by
  intro F _ _ _ M σ hσ ι _ u hu hL
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hLi : ∀ i, abelian₂ M (u i) ≠ ⊤ := fun i => ne_top_of_le_ne_top hL (ENNReal.le_tsum i)
  have hC := fun i => _root_.UpperTheory.ConvolutionTheory.R2.M.unfC F M σ (u i) hσ (hu i).1 (hu i).2 (hLi i)
  have hTL : ∀ i, ∫⁻ g in M.D, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ∂M.μ = abelian₂ M (u i) := fun i =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.unfL F M σ (fun g => ‖u i g‖ₑ) hσ (hu i).1.enorm
      (fun ξ g => by simp only [(hu i).2 ξ g])
  have hTm : ∀ i, Measurable fun g : G1 F => ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ := fun i =>
    Measurable.ennreal_tsum fun r => ((hu i).1.comp (measurable_const_mul _)).enorm
  have hTT : ∫⁻ g in M.D, ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ∂M.μ = ∑' i, abelian₂ M (u i) := by
    rw [lintegral_tsum fun i => (hTm i).aemeasurable]
    exact tsum_congr hTL
  have hfin : ∀ᵐ g ∂(M.μ.restrict M.D), ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ≠ ⊤ := by
    have hm : AEMeasurable (fun g : G1 F => ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ) (M.μ.restrict M.D) :=
      (Measurable.ennreal_tsum hTm).aemeasurable
    filter_upwards [ae_lt_top' hm (by rw [hTT]; exact hL)] with g hg using hg.ne
  have hST : ∀ i g, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ≤ ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ := fun i g =>
    enorm_tsum_le' _
  have hSL : ∀ i, ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≤ abelian₂ M (u i) := fun i =>
    (lintegral_mono fun g => hST i g).trans_eq (hTL i)
  have hsum : ∑' i, ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≠ ⊤ :=
    ne_top_of_le_ne_top hL (ENNReal.tsum_le_tsum hSL)
  have hSm : ∀ i, AEStronglyMeasurable (fun g => ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) :=
    fun i => (hC i).2.1.aestronglyMeasurable
  have hI := integral_tsum hSm hsum
  have hae : ∀ᵐ g ∂(M.μ.restrict M.D),
      ∑' r, ∑' i, u i (ratS F (σ r) * g) = ∑' i, ∑' r, u i (ratS F (σ r) * g) := by
    filter_upwards [hfin] with g hg using
      tsum_comm_of_enorm (fun i r => u i (ratS F (σ r) * g)) hg
  have hI0 : ∀ i, M.I0 (av (u i)) = ∫ g in M.D, ∑' r, u i (ratS F (σ r) * g) ∂M.μ := fun i =>
    ((hC i).2.2.2).symm
  refine ⟨?_, ?_, ?_⟩
  · have hle : ∀ i, ‖M.I0 (av (u i))‖ₑ ≤ ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ := fun i => by
      rw [hI0 i]
      exact enorm_integral_le_lintegral_enorm _
    have : ∑' i, ‖M.I0 (av (u i))‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hle)
    simpa [toReal_enorm] using ENNReal.summable_toReal this
  · have hsm : AEStronglyMeasurable (fun g => ∑' i, ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) := by
      refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
        (f := fun (s : Finset ι) g => ∑ i ∈ s, ∑' r, u i (ratS F (σ r) * g)) ?_ ?_
      · intro s
        exact Finset.aestronglyMeasurable_fun_sum s fun i _ => hSm i
      · filter_upwards [hfin] with g hg
        have h1 : ∑' i, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ≠ ⊤ :=
          ne_top_of_le_ne_top hg (ENNReal.tsum_le_tsum fun i => hST i g)
        have h2 : Summable fun i => ‖∑' r, u i (ratS F (σ r) * g)‖ := by
          simpa [toReal_enorm] using ENNReal.summable_toReal h1
        exact (Summable.of_norm h2).hasSum
    have hint : Integrable (fun g => ∑' i, ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) := by
      refine ⟨hsm, ?_⟩
      have hb : ∫⁻ g in M.D, ‖∑' i, ∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≤ ∑' i, abelian₂ M (u i) := by
        rw [← hTT]
        refine lintegral_mono fun g => ?_
        exact (enorm_tsum_le' _).trans (ENNReal.tsum_le_tsum fun i => hST i g)
      exact lt_of_le_of_lt hb hL.lt_top
    exact hint.congr (hae.mono fun g hg => hg.symm)
  · rw [integral_congr_ae hae, hI]
    exact tsum_congr fun i => (hI0 i).symm
