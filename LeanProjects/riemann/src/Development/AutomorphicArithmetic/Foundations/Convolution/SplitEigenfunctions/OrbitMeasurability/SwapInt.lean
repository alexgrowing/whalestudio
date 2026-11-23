import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.BddE
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ZDom
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.GaloisBaseChangeSchemeActionCompSnd
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ContInfPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem int_prod {Z P : Type} [MeasurableSpace Z] [MeasurableSpace P] (m : Measure Z) [IsFiniteMeasure m]
    (n : Measure P) [SFinite n] {F : Z × P → ℂ} (hF : Measurable F) {K : ℝ≥0∞} (hK : K < ⊤)
    (h : ∀ᵐ z ∂m, ∫⁻ p, ‖F (z, p)‖ₑ ∂n ≤ K) : Integrable F (m.prod n) := by
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hF.enorm.aemeasurable]
  refine (lintegral_mono_ae h).trans_lt ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hK (measure_lt_top _ _)

private theorem swap_int {Z X T : Type} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace T] (m : Measure Z) [IsFiniteMeasure m]
    (n : Measure X) [SFinite n] (l : Measure T) [IsFiniteMeasure l] {c : X → ℂ} (hcm : Measurable c) (hc : Integrable c n)
    {G : (Z × X) × T → ℂ} (hG : Measurable G) {S : Set Z} (hS : ∀ᵐ z ∂m, z ∈ S) {B : ℝ}
    (hB : ∀ z ∈ S, ∀ y, c y ≠ 0 → ∀ g, ‖G ((z, y), g)‖ ≤ B) :
    ∫ z, ∫ y, c y * ∫ g, G ((z, y), g) ∂l ∂n ∂m = ∫ y, c y * ∫ z, ∫ g, G ((z, y), g) ∂l ∂m ∂n := by
  have h1 : StronglyMeasurable fun p : Z × X => ∫ g, G (p, g) ∂l := hG.stronglyMeasurable.integral_prod_right'
  have h2 : Integrable (fun p : Z × X => B * l.real Set.univ * ‖c p.2‖) (m.prod n) :=
    (hc.norm.comp_snd m).const_mul _
  have h3 : ∀ᵐ p : Z × X ∂(m.prod n), p.1 ∈ S :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hS
  rw [integral_integral_swap]
  · refine integral_congr_ae (ae_of_all _ fun y => ?_)
    exact integral_const_mul _ _
  · refine h2.mono' (((hcm.comp measurable_snd).mul h1.measurable).aestronglyMeasurable) ?_
    filter_upwards [h3] with p hp
    by_cases h0 : c p.2 = 0
    · simp [Function.uncurry, h0]
    · simp only [Function.uncurry, norm_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (norm_integral_le_of_norm_le_const (ae_of_all _ fun g => hB p.1 hp p.2 h0 g)) (norm_nonneg _)

private theorem cont_em {E : Type} [Field E] [NumberField E] : Continuous (em E) := by
  have hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap
  exact Continuous.units_map _ hM

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zAll :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZAll := by
  intro E _ _ _ D W M N P φ hφ j hj c hc hcs Ψ hΨ hΨc
  obtain ⟨hfin, hS, C, hC, hSC⟩ := zDom E
  obtain ⟨hm1, hm2, -⟩ := yInt E D W M N P φ hφ
  have hsZ : Continuous (sZ D) := (szLaws E D).2.1
  have hφc : Continuous φ.1 := (decE E P φ hφ).1.1
  have hone := zOne E D W M N P φ hφ j hj c hc hcs Ψ hΨc
  haveI := N.haar
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) := ⟨by simpa using hfin⟩
  haveI : Countable (Orb D.δ) := inferInstance
  have hci : Integrable c N.μ := hc.integrable_of_hasCompactSupport hcs
  obtain ⟨B, hB⟩ := bddE E P φ hφ _ (hC.image hsZ)
  obtain ⟨B', hB'⟩ := bddE E P φ hφ _
    ((hC.prod hcs.isCompact).image (f := fun p : (A E)ˣ × G1 E => sZ D p.1 * gl p.2)
      ((hsZ.comp continuous_fst).mul (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd)))
  have hI : Integrable (fun y => Ψ (pY D y) * φ.1 (el D y)) (mY D.δ N) := by
    refine int_prod _ _ ((hΨ.comp hm1).mul hm2) (K := ENNReal.ofReal B * M.μ M.D * ∫⁻ y, ‖c y‖ₑ ∂N.μ) ?_ ?_
    · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (UpperTheory.ConvolutionTheory.R2.M.volD ℚ M)) hci.2
    · filter_upwards [ae_restrict_mem hS] with z hz
      exact (hone z).1 B fun h => hB h _ ⟨_, hSC z hz, rfl⟩
  refine ⟨hI, ?_⟩
  have hG : Continuous fun p : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × G1 ℚ =>
      φ.1 (em E (gl p.2) * sZ D (p.1.1 : IdeleGroup E) * gl p.1.2) :=
    hφc.comp (((cont_em.comp (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd)).mul
      (hsZ.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)))).mul
      (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp (continuous_snd.comp continuous_fst)))
  have hsw := swap_int ((normOneMeasure E).restrict (normOneFundamentalDomain E)) N.μ (M.μ.restrict M.D) hc.measurable hci
    hG.measurable (ae_restrict_mem hS) (B := B') (fun z hz y hy g => by
      have h := hB' (j g) _ ⟨((z : IdeleGroup E), y), ⟨hSC z hz, subset_tsupport _ hy⟩, rfl⟩
      rwa [hj, ← mul_assoc] at h)
  unfold mY at hI ⊢
  rw [integral_prod _ hI]
  simp only [fun z => (hone z).2]
  exact hsw

end
