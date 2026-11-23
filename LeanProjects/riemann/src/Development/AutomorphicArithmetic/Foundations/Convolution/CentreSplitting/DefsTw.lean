import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.V

namespace UpperTheory.ConvolutionTheory.Dp

def TwUnitary : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ), (∀ v, ‖θ.U v‖ = ‖v‖) ∧ Function.Surjective θ.U ∧
      ∀ g v, θ.U (rightRegularRep (rationalGLOne K n) μ g v) = rightRegularRep (rationalGLOne K n) μ (θ.e g) (θ.U v)

def TwCls : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ), ∀ φ ∈ centralCuspForms K n, ∀ ψ ∈ centralCuspForms K n,
      (θ.U (clsL μ ψ) = clsL μ φ ↔ ∀ x : normOneGL K n, ψ.1 x = φ.1 (θ.e x : normOneGL K n))

def TwSummand : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ) (V : Submodule ℂ (LL μ)), IsSummand μ V ↔ IsSummand μ (V.map θ.U.toLinearMap)

def GalCentral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (σ : E ≃+* E) (s : Ad E ≃+* Ad E),
    UpperTheory.CBC.IsGalAd σ s → (∀ s', UpperTheory.CBC.IsGalAd σ s' → s' = s) ∧
      ∀ t, Matrix.GeneralLinearGroup.map s.toRingHom (centralSection E n t) = centralSection E n t

def ConjCarries : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ) (σ : E ≃+* E) (s : Ad E ≃+* Ad E), UpperTheory.CBC.IsGalAd σ s →
    (∀ g : normOneGL E n, ((θ.e g : normOneGL E n) : GA E n) = Matrix.GeneralLinearGroup.map s.toRingHom (g : GA E n)) →
    ∀ (π π' : CuspSub E n) (V' : Submodule ℂ (LL μ)),
      (UpperTheory.CBC.Cusp.cx π').space =
        (fun f : GA E n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (UpperTheory.CBC.Cusp.cx π).space →
      (Carries μ π' V' ↔ Carries μ π (V'.map θ.U.toLinearMap))

def ConjIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ) (σ : E ≃+* E) (s : Ad E ≃+* Ad E), UpperTheory.CBC.IsGalAd σ s →
    (∀ g : normOneGL E n, ((θ.e g : normOneGL E n) : GA E n) = Matrix.GeneralLinearGroup.map s.toRingHom (g : GA E n)) →
    ∀ (π : CuspSub E n) (V : Submodule ℂ (LL μ)), Carries μ π V →
      ((UpperTheory.CBC.Cusp.cx π).ConjIso σ ↔ V.map θ.U.toLinearMap = V)

end UpperTheory.ConvolutionTheory.Dp
