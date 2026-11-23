import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

open private UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.eig_int UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_n UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_mkE UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_ψ from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE

theorem UpperTheory.eigAt_cmDatumOperator_of_eigAt :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (w : H.P E) (B : Multiset ℂˣ), Continuous φ → EigAt w B φ → EigAt w B (Wo D φ) := by
  intro E _ _ D φ w B hφ hB g
  have hi : ∀ h : GL (Fin 2) (A E),
      IntegrableOn (fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
    intro h
    obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
      ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
        (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
        fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
    have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
    have hc : Continuous fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1) :=
      (hφ.comp ((UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_n.comp (UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_mkE D)).mul continuous_const)).mul
        (UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.cont_ψ.comp (continuous_apply 1))
    exact (hc.continuousOn.integrableOn_compact hK).mono_set fun x hx i hi => hEC (hx i hi)
  refine UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen.eig_int ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) (hB 1).card
    (fun x y => φ (nE D x * (g * finGL E 2 (locGL E 2 w y)))) (fun x => ψ (x 1))
    (fun x => ?_) fun y => hi _
  simpa only [mul_assoc] using hB (nE D x * g)
