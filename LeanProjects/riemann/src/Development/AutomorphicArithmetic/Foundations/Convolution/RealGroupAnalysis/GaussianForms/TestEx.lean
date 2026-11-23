import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GaussS
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.TestFunctionExistence

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private noncomputable abbrev g0 (F : Type) [Field F] [NumberField F] : FiniteAdeleRing (𝓞 F) F → ℂ :=
  cosetIndicator (1 : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) 0

private theorem gaussianTest_real_nonneg (x : A F) : ∃ r : ℝ, 0 ≤ r ∧ g1 (g0 F) x = (r : ℂ) := by
  refine ⟨(∏ w, Real.exp (-Real.pi * (TR.pInf F x w) ^ 2)) *
    (if x.2 - 0 ∈ idealFiniteAdeles (1 : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) then 1 else 0), ?_, ?_⟩
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le) (by split_ifs <;> norm_num)
  · simp only [g1, g0, cosetIndicator_apply]
    push_cast
    split_ifs <;> simp

private theorem four_real (v : V4 F) : ∃ r : ℝ, 0 ≤ r ∧ four (g1 (g0 F)) v = (r : ℂ) := by
  obtain ⟨a, ha, ea⟩ := gaussianTest_real_nonneg (F := F) (rt (2⁻¹ : F) * (v 1 - v 0))
  obtain ⟨b, hb, eb⟩ := gaussianTest_real_nonneg (F := F) (rt (2⁻¹ : F) * (v 1 + v 0))
  obtain ⟨c, hc, ec⟩ := gaussianTest_real_nonneg (F := F) (v 2)
  obtain ⟨d, hd, ed⟩ := gaussianTest_real_nonneg (F := F) (v 3)
  refine ⟨a * b * c * d, by positivity, ?_⟩
  simp only [four, ea, eb, ec, ed]
  push_cast
  rfl

private theorem gaussianTest_zero : g1 (g0 F) (0 : A F) = 1 := by
  have h : TR.pInf F (0 : A F) = 0 := by
    simp
  simp [g1, g0, cosetIndicator_apply, h]

private theorem four_zero : four (g1 (g0 F)) (0 : V4 F) = 1 := by
  simp [four, gaussianTest_zero]

private def Mt (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-2⁻¹, 2⁻¹, 0, 0; 2⁻¹, 2⁻¹, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def Nt (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-1, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem NM : Nt F * Mt F = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nt, Mt, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> norm_num

private theorem MN : Mt F * Nt F = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nt, Mt, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> norm_num

private theorem four_mem : four (g1 (g0 F)) ∈ schwartzBruhatPi F (Fin 4) := by
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi (Mt F) (Nt F) NM MN
    (gaussS F (Fin 4) (g0 F) (cosetIndicator_mem_finiteSchwartzBruhat _ _))
  convert h using 1
  funext v
  have hv : ((Mt F).map (algebraMap F (A F)) *ᵥ v) =
      ![rt (2⁻¹ : F) * (v 1 - v 0), rt (2⁻¹ : F) * (v 1 + v 0), v 2, v 3] := by
    funext i
    fin_cases i <;>
      simp [Mt, Matrix.mulVec, dotProduct, Fin.sum_univ_four, rt, mul_sub, mul_add] <;> ring
  rw [hv]
  simp [four, Fin.prod_univ_four]

end UpperTheory.ConvolutionTheory.R2.C.TestFunctionExistence

open UpperTheory.ConvolutionTheory.R2.C.TestFunctionExistence in
theorem UpperTheory.ConvolutionTheory.R2.C.testEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ g : FiniteAdeleRing (𝓞 F) F → ℂ, four (g1 g) ∈ schwartzBruhatPi F (Fin 4) ∧ ∫ v, four (g1 g) v ∂(adeleMeasurePi F) ≠ 0 ∧ Th (four (g1 g)) ≠ 0 := by
  intro F _ _ _
  have hm := four_mem (F := F)
  have hre : ∀ v : V4 F, four (g1 (g0 F)) v = (((four (g1 (g0 F)) v).re : ℝ) : ℂ) := by
    intro v
    obtain ⟨r, -, e⟩ := four_real (F := F) v
    rw [e]
    simp
  have hnn : ∀ v : V4 F, 0 ≤ (four (g1 (g0 F)) v).re := by
    intro v
    obtain ⟨r, h, e⟩ := four_real (F := F) v
    rw [e]
    simpa using h
  have hc : Continuous fun v : V4 F => (four (g1 (g0 F)) v).re :=
    Complex.continuous_re.comp (continuous_of_mem_schwartzBruhatPi hm)
  have hi : Integrable (fun v : V4 F => (four (g1 (g0 F)) v).re) (adeleMeasurePi F) :=
    (integrable_of_mem_schwartzBruhatPi hm).re
  refine ⟨g0 F, hm, ?_, ?_⟩
  · have hpos : 0 < ∫ v, (four (g1 (g0 F)) v).re ∂(adeleMeasurePi F) := by
      rw [integral_pos_iff_support_of_nonneg hnn hi]
      have ho : IsOpen (Function.support fun v : V4 F => (four (g1 (g0 F)) v).re) :=
        isOpen_compl_singleton.preimage hc
      refine ho.measure_pos _ ⟨0, ?_⟩
      simp [Function.mem_support, four_zero]
    have he : ∫ v, four (g1 (g0 F)) v ∂(adeleMeasurePi F) =
        ((∫ v, (four (g1 (g0 F)) v).re ∂(adeleMeasurePi F) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall hre)
    rw [he]
    exact_mod_cast hpos.ne'
  · have hs : Summable fun ξ : Fin 4 → F => four (g1 (g0 F)) fun i => rt (ξ i) :=
      (poisson_of_mem_schwartzBruhatPi hm).1.of_norm
    have hsr : Summable fun ξ : Fin 4 → F => (four (g1 (g0 F)) fun i => rt (ξ i)).re :=
      Complex.reCLM.summable hs
    have h1 : (1 : ℝ) ≤ ∑' ξ : Fin 4 → F, (four (g1 (g0 F)) fun i => rt (ξ i)).re := by
      have h := hsr.le_tsum (0 : Fin 4 → F) fun ξ _ => hnn _
      have h0 : (fun i : Fin 4 => rt ((0 : Fin 4 → F) i)) = (0 : V4 F) := by
        funext i
        simp [rt]
      rw [h0, four_zero] at h
      simpa using h
    intro hT
    have h2 : (Th (four (g1 (g0 F)))).re = ∑' ξ : Fin 4 → F, (four (g1 (g0 F)) fun i => rt (ξ i)).re :=
      Complex.re_tsum hs
    rw [hT] at h2
    simp at h2
    linarith
