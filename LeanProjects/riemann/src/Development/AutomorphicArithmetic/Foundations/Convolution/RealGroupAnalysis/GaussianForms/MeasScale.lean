import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.measScale :
    ∀ (F : Type) [Field F] [NumberField F] (a : (A F)ˣ) (f : V4 F → ℂ), ∫ v, f (fun i => (a : A F) * v i) ∂(adeleMeasurePi F) = (((ab a)⁻¹ ^ 4 : ℝ) : ℂ) * ∫ v, f v ∂(adeleMeasurePi F) := by
  intro F _ _ a f
  have hpos : 0 ≤ ((IdeleGroup.ideleModule F a : ℝ))⁻¹ := inv_nonneg.mpr (IdeleGroup.ideleModule F a).2.le
  have hmap := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_diagonal (K := F) (n := 4) (fun _ => a)
  have hf : (fun x : V4 F => x ᵥ* Matrix.diagonal (fun _ : Fin 4 => ((a : (A F)ˣ) : A F))) =
      fun x i => (a : A F) * x i := by
    funext x i
    rw [vecMul_diagonal, mul_comm]
  let e : V4 F ≃ᵐ V4 F := MeasurableEquiv.piCongrRight fun _ => (Homeomorph.smul a).toMeasurableEquiv
  have he : (e : V4 F → V4 F) = fun x i => (a : A F) * x i := rfl
  have h1 : ∫ v, f (fun i => (a : A F) * v i) ∂(adeleMeasurePi F) =
      ∫ v, f v ∂((adeleMeasurePi F).map (fun x : V4 F => fun i => (a : A F) * x i)) := by
    rw [← he]
    exact (e.measurableEmbedding.integral_map f).symm
  rw [h1, ← hf, hmap, integral_smul_measure, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hpos, ENNReal.toReal_ofReal (pow_nonneg hpos 4), Complex.real_smul]
  rfl
