import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.EtaEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContinuousQuaternaryFormLeft
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GenRel
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.OpsRel
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.OpsGauss
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.IdxEta
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Generic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormRationalEmbed
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsBis
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContinuousFiniteAdeleEmbed
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.AbMul
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierConstMul
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActRat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.weilEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), St.WeilEx D := by
  intro F E _ _ _ _ _ _ _ D
  have hδ : D.δ ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    intro h
    have := D.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨η, hq, hsq, hn, hk⟩ := etaEx F E D
  obtain ⟨O⟩ := opsEx F D.δ η.1 hδ
  obtain ⟨Om, h1, h2, h3⟩ := chunk F _ O.N O.M O.W (opsRel F D.δ η.1 O hδ hsq)
    (opsGauss F D.δ η.1 O hδ hsq (idxEta F E D η.1 hsq hk)) (generic F)
  have hO : IsOm D.δ η.1 Om :=
    ⟨fun b φ v => h1 b ▸ O.N_apply b φ v, fun a φ v => h2 a ▸ O.M_apply a φ v, fun φ v => h3 ▸ O.W_apply φ v⟩
  obtain ⟨L, hL⟩ := UpperTheory.ConvolutionTheory.R2.D.lEx F E D
  exact ⟨{
    η := η, Om := Om, L := L, quad := hq, η_sq := hsq, η_norm := hn, Om_n := hO.n, Om_m := hO.m, Om_w := hO.w, L_apply := hL
    comm := UpperTheory.ConvolutionTheory.R2.D.comm F E D η.1 Om L hn hO.n hO.m hO.w hL
    th_Om := thOm F D.δ η.1 Om hδ hO
    th_L := fun γ φ => by
      rw [← UpperTheory.ConvolutionTheory.R2.D.thL F E D γ φ.1]
      exact congrArg Th (funext (hL _ φ))
    level := level F D.δ η.1 Om hO
    unr := fun φ => unrOf F _ (level F D.δ η.1 Om hO φ)
    cont := cont F D.δ η.1 Om η.2.1 hO }⟩
