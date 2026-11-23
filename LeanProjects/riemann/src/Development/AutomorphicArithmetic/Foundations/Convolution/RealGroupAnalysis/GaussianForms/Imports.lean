import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContKer
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsBis

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.cont :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)), Continuous η → IsOm δ η Om →
    ∀ φ, Continuous fun p : G1 F × V4 F => (Om p.1 φ).1 p.2 := by
  intro F _ _ δ η Om hη hOm φ
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, v₀⟩
  obtain ⟨b, c, a, k, hb, hc, ha, hk, hev⟩ := near F
  set φ' : S4 F := Om g₀ φ with hφ'
  set φ'' : S4 F := Om (wW F)⁻¹ φ' with hφ''

  let H : G1 F × V4 F → G1 F := fun p => p.1 * g₀⁻¹
  have hH1 : H (g₀, v₀) = 1 := by simp [H]
  have hH : Tendsto H (𝓝 (g₀, v₀)) (𝓝 1) := by
    have : ContinuousAt H (g₀, v₀) := by
      have : Continuous H := continuous_fst.mul continuous_const
      exact this.continuousAt
    simpa [ContinuousAt, hH1] using this

  let f : G1 F × V4 F → ℂ := fun p =>
    ψ (b (H p) * q4 δ p.2) * (((η (a (H p)) : ℂˣ) : ℂ) * ((ab (a (H p)) ^ 2 : ℝ) : ℂ) *
      ft4 δ (fun y => ψ (c (H p) * q4 δ y) * φ''.1 y) (fun i => (a (H p) : A F) * p.2 i))
  have hbH : ContinuousAt (fun p => b (H p)) (g₀, v₀) := by
    show Tendsto (fun p => b (H p)) _ (𝓝 (b (H (g₀, v₀))))
    rw [hH1]
    exact hb.tendsto.comp hH
  have hcH : ContinuousAt (fun p => c (H p)) (g₀, v₀) := by
    show Tendsto (fun p => c (H p)) _ (𝓝 (c (H (g₀, v₀))))
    rw [hH1]
    exact hc.tendsto.comp hH
  have haH : ContinuousAt (fun p => a (H p)) (g₀, v₀) := by
    show Tendsto (fun p => a (H p)) _ (𝓝 (a (H (g₀, v₀))))
    rw [hH1]
    exact ha.tendsto.comp hH
  have hf : ContinuousAt f (g₀, v₀) := by
    have hs : ContinuousAt (fun p : G1 F × V4 F => p.2) (g₀, v₀) := continuous_snd.continuousAt
    have hav : ContinuousAt (fun p => ((a (H p) : (A F)ˣ) : A F)) (g₀, v₀) :=
      Units.continuous_val.continuousAt.comp haH
    have h1 : ContinuousAt (fun p : G1 F × V4 F => ψ (b (H p) * q4 δ p.2)) (g₀, v₀) :=
      continuous_ψ.continuousAt.comp (hbH.mul ((continuous_quaternaryQuadraticForm δ).continuousAt.comp hs))
    have h2 : ContinuousAt (fun p : G1 F × V4 F => ((η (a (H p)) : ℂˣ) : ℂ)) (g₀, v₀) :=
      (Units.continuous_val.comp hη).continuousAt.comp haH
    have h3 : ContinuousAt (fun p : G1 F × V4 F => ((ab (a (H p)) ^ 2 : ℝ) : ℂ)) (g₀, v₀) :=
      Complex.continuous_ofReal.continuousAt.comp ((continuous_ab.continuousAt.comp haH).pow 2)
    have hvec : ContinuousAt (fun p : G1 F × V4 F => (fun i => (a (H p) : A F) * p.2 i : V4 F)) (g₀, v₀) := by
      refine continuousAt_pi.2 fun i => hav.mul ?_
      exact (continuous_apply i).continuousAt.comp hs
    have h4 : ContinuousAt (fun p : G1 F × V4 F =>
        ft4 δ (fun y => ψ (c (H p) * q4 δ y) * φ''.1 y) (fun i => (a (H p) : A F) * p.2 i)) (g₀, v₀) :=
      ContinuousAt.comp (f := fun p : G1 F × V4 F => (c (H p), (fun i => (a (H p) : A F) * p.2 i : V4 F)))
        (g := fun p : A F × V4 F => ft4 δ (fun y => ψ (p.1 * q4 δ y) * φ''.1 y) p.2)
        (contKer F δ φ'').continuousAt (hcH.prodMk hvec)
    exact h1.mul ((h2.mul h3).mul h4)
  refine hf.congr ?_

  have hlev : ∀ᶠ h in 𝓝 (1 : G1 F), InfOne (k h) → Om (k h) φ' = φ' := by
    exact hk.eventually (level F δ η Om hOm φ')
  filter_upwards [hH.eventually (hev.and hlev)] with p hp
  obtain ⟨⟨hinf, hdec⟩, hl⟩ := hp
  have hg : p.1 = H p * g₀ := by simp [H]
  have hkey : Om p.1 φ = Om (nU (b (H p))) (Om (mD (a (H p))) (Om (wW F) (Om (nU (c (H p))) φ''))) := by
    rw [hg, map_mul, Module.End.mul_apply, ← hφ']
    conv_lhs => rw [hdec]
    simp only [map_mul, Module.End.mul_apply]
    rw [hl hinf]
  show f p = (Om p.1 φ).1 p.2
  rw [hkey, hOm.n, hOm.m, hOm.w]
  show _ = ψ _ * (_ * _ * ft4 δ (Om (nU (c (H p))) φ'').1 _)
  have : (Om (nU (c (H p))) φ'').1 = fun y => ψ (c (H p) * q4 δ y) * φ''.1 y := funext (hOm.n _ _)
  rw [this]
