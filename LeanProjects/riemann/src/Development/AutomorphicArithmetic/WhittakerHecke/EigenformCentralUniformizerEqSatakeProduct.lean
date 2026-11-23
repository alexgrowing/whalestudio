import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.eigenform_central_uniformizer_eq_satake_product :
    ∀ (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ), H.IsU ϖ → ∀ (α β : ℂˣ) (f : GL (Fin 2) (A K) → ℂ),
          EigAt v {α, β} f → ∀ h, f (Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl v ϖ) * h) = (α : ℂ) * β * f h := by
  intro K _ _ v ϖ hϖ α β f hEig h
  obtain ⟨R, -, -, hR⟩ := H.heckeExpl K v ϖ hϖ
  have hc := (hR α β _ (hEig h) 1).2
  have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl v ϖ) * h =
      h * Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl v ϖ) :=
    Units.ext (Matrix.scalar_commute ((H.idl v ϖ : (A K)ˣ) : A K) (fun r => Commute.all _ r) (h : Matrix (Fin 2) (Fin 2) (A K))).eq
  rw [hcomm]
  simp only [one_mul, map_one, mul_one] at hc
  rw [← (H.lcLaws K v).2.2.2.2.1]
  exact hc
