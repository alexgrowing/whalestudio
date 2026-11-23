import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.JGenLinLie
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE

open GroundTheory.Automorphic

private theorem UpperTheory.ConvolutionTheory.L1.jUnique_mem_of_e {n : ℕ} (S : Subalgebra ℂ (HarishChandra.U n))
    (h : ∀ a b, HarishChandra.e (a, b) ∈ S) (x : HarishChandra.U n) : x ∈ S := by
  induction x using HarishChandra.U.induction with
  | halg r => exact S.algebraMap_mem r
  | hι X =>
    rw [HarishChandra.ι_eq_sum_e]
    exact S.sum_mem fun a _ => S.smul_mem (h a.1 a.2) _
  | hmul a b ha hb => exact S.mul_mem ha hb
  | hadd a b ha hb => exact S.add_mem ha hb

theorem UpperTheory.ConvolutionTheory.L1.jUnique :
    UpperTheory.ConvolutionTheory.L1.JUnique := by
  intro K _ _ _ n τ
  obtain ⟨⟨j, hj⟩, hiff⟩ := UpperTheory.ConvolutionTheory.Dp.jGen K n τ
  refine ⟨⟨j, hj, fun j' hj' => ?_⟩, (UpperTheory.ConvolutionTheory.Dp.capZc K n τ).1⟩
  refine AlgHom.ext fun x => ?_
  exact UpperTheory.ConvolutionTheory.L1.jUnique_mem_of_e (AlgHom.equalizer j' j)
    (fun a b => ((hiff j').1 hj' a b).trans ((hiff j).1 hj a b).symm) x
