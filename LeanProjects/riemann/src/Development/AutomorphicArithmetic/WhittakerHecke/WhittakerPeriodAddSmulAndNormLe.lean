import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem volume_fundamental_domain_two : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 :=
  GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain

private theorem cont_nE {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
  UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))

private theorem int_Wo {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) {f : GL (Fin 2) (A E) → ℂ}
    (hf : Continuous f) (h : GL (Fin 2) (A E)) :
    IntegrableOn (fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
  have hg : Continuous fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1) :=
    (hf.comp ((cont_nE D).mul continuous_const)).mul
      (UpperTheory.ConvolutionTheory.R2.Pp.cont_ψ.comp (continuous_apply 1))
  obtain ⟨C, hC, hs⟩ := UpperTheory.ConvolutionTheory.R2.Pp.exists_cpt (F := ℚ)
  have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
  have hsub : FS2 ℚ ⊆ Set.univ.pi fun _ : Fin 2 => C := Set.pi_mono fun _ _ => hs
  unfold adeleMeasurePi
  exact (hg.continuousOn.integrableOn_compact hK).mono_set hsub

theorem UpperTheory.whittakerPeriod_add_smul_and_norm_le :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E),
        (∀ f f' : GL (Fin 2) (A E) → ℂ, Continuous f → Continuous f' → ∀ h, Wo D (f + f') h = Wo D f h + Wo D f' h) ∧
        (∀ (c : ℂ) (f : GL (Fin 2) (A E) → ℂ) h, Wo D (c • f) h = c * Wo D f h) ∧
        ∀ (f : GL (Fin 2) (A E) → ℂ) (B : ℝ) h, (∀ g, ‖f g‖ ≤ B) → ‖Wo D f h‖ ≤ B := by
  intro E _ _ D
  refine ⟨fun f f' hf hf' h => ?_, fun c f h => ?_, fun f B h hB => ?_⟩
  · unfold Wo
    rw [← integral_add (int_Wo D hf h) (int_Wo D hf' h)]
    simp only [Pi.add_apply, add_mul]
  · unfold Wo
    rw [← integral_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · have := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasurePi (ι := Fin 2) ℚ) (s := FS2 ℚ)
      (f := fun u => f (nE D u * h) * ψ (u 1)) (C := B) (by rw [volume_fundamental_domain_two]; exact ENNReal.one_lt_top)
      fun u _ => by rw [norm_mul, UpperTheory.ConvolutionTheory.R2.Pp.norm_ψ, mul_one]; exact hB _
    rwa [measureReal_def, volume_fundamental_domain_two, ENNReal.toReal_one, mul_one] at this
