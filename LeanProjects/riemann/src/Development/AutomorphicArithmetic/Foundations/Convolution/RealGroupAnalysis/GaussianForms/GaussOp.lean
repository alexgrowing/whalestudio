import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormShiftExpand
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem quadraticForm_neg (δ : F) (y : V4 F) : q4 δ (-y) = q4 δ y := by
  simp only [q4, Pi.neg_apply]
  ring

private theorem quaternaryForm_neg_right (δ : F) (y v : V4 F) : B4 δ (-y) (-v) = B4 δ y v := by
  simp only [B4, Pi.neg_apply]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.gaussOp :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ (b : (A F)ˣ) (c : ℂ), IsIdx δ (b : A F) c → ∀ (φ : S4 F) (v : V4 F),
    Pc δ (b : A F) φ.1 v = c * ft4 δ (fun y => ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 y) v := by
  intro F _ _ δ hδ b c hc φ v
  have hmem := (pcMem F δ).2 hδ b φ.1 φ.2
  have h2 := (ftBasic F δ hδ _ hmem).2.1 (-v)
  rw [neg_neg] at h2
  rw [← h2]
  have e1 : ∀ y, ft4 δ (Pc δ (b : A F) φ.1) y * ψ (B4 δ y (-v)) =
      c * ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 (-y) * ψ (B4 δ y (-v)) := fun y => by
    rw [idxFt F δ b c hc φ y]
  conv_lhs => rw [ft4]
  simp only [e1]
  rw [← integral_neg_eq_self _ (adeleMeasurePi F)]
  simp only [neg_neg, quadraticForm_neg, quaternaryForm_neg_right]
  rw [ft4, ← integral_const_mul]
  congr 1
  funext y
  ring
