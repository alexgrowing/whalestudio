import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FockEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkD
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkLe

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

private def stab {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F) :
    Subalgebra ℂ (Module.End ℂ (S4 F)) where
  carrier := {T | ∀ φ ∈ Fock δ, T φ ∈ Fock δ}
  mul_mem' := fun ha hb φ h => ha _ (hb φ h)
  add_mem' := fun ha hb φ h => Submodule.add_mem _ (ha φ h) (hb φ h)
  algebraMap_mem' := fun c φ h => by
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ c h

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.fockOps :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Ops F), ∀ φ ∈ Fock D.δ, (∀ w i, O.x w i φ ∈ Fock D.δ) ∧ (∀ w i, O.d w i φ ∈ Fock D.δ) ∧ (∀ w, O.e D.δ w φ ∈ Fock D.δ) ∧
    (∀ w, O.f D.δ w φ ∈ Fock D.δ) ∧ (∀ w, O.h w φ ∈ Fock D.δ) ∧ (∀ τ i j, O.dE D τ i j φ ∈ Fock D.δ) ∧ ∀ Y, O.dL D Y φ ∈ Fock D.δ := by
  intro F E _ _ _ _ _ _ _ D O
  have hx : ∀ w i, O.x w i ∈ stab D.δ := fun w i => (fkLe F D.δ O).1 w i
  have hd : ∀ w i, O.d w i ∈ stab D.δ := by
    intro w i φ hφ
    obtain ⟨Λ, m, h⟩ := fockEx F E D O {φ} (Set.finite_singleton φ)
      (fun ψ hψ => (Set.mem_singleton_iff.1 hψ) ▸ hφ)
    exact (fkLe F D.δ O).2 _ inf_le_left (m + 1)
      (fkD F D.δ O _ inf_le_left m w i φ (h φ (Set.mem_singleton φ)))
  have he : ∀ w, O.e D.δ w ∈ stab D.δ := fun w =>
    Subalgebra.smul_mem _ (sub_mem (sub_mem (mul_mem (hx w 2) (hx w 2))
      (Subalgebra.smul_mem _ (mul_mem (hx w 3) (hx w 3)) _)) (mul_mem (hx w 1) (hx w 0))) _
  have hf : ∀ w, O.f D.δ w ∈ stab D.δ := fun w =>
    Subalgebra.smul_mem _ (sub_mem (sub_mem (Subalgebra.smul_mem _ (mul_mem (hd w 2) (hd w 2)) _)
      (Subalgebra.smul_mem _ (mul_mem (hd w 3) (hd w 3)) _)) (mul_mem (hd w 1) (hd w 0))) _
  have hh : ∀ w, O.h w ∈ stab D.δ := fun w =>
    add_mem (sum_mem fun i _ => mul_mem (hx w i) (hd w i)) (ofNat_mem _ 2)
  have hX : ∀ τ a b, O.X D τ a b ∈ stab D.δ := by
    intro τ a b
    fin_cases a <;> fin_cases b
    · exact hx _ 1
    · exact add_mem (hx _ 2) (Subalgebra.smul_mem _ (hx _ 3) _)
    · exact sub_mem (hx _ 2) (Subalgebra.smul_mem _ (hx _ 3) _)
    · exact hx _ 0
  have hDX : ∀ τ a b, O.DX D τ a b ∈ stab D.δ := by
    intro τ a b
    fin_cases a <;> fin_cases b
    · exact hd _ 1
    · exact Subalgebra.smul_mem _ (add_mem (hd _ 2) (Subalgebra.smul_mem _ (hd _ 3) _)) _
    · exact Subalgebra.smul_mem _ (sub_mem (hd _ 2) (Subalgebra.smul_mem _ (hd _ 3) _)) _
    · exact hd _ 0
  have hE : ∀ τ i j, O.dE D τ i j ∈ stab D.δ := by
    intro τ i j
    refine sub_mem (neg_mem ?_) (sum_mem fun b _ => mul_mem (hX τ j b) (hDX τ i b))
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hL : ∀ Y, O.dL D Y ∈ stab D.δ := fun Y =>
    sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ => Subalgebra.smul_mem _ (hE τ i j) _
  intro φ hφ
  exact ⟨fun w i => hx w i φ hφ, fun w i => hd w i φ hφ, fun w => he w φ hφ, fun w => hf w φ hφ,
    fun w => hh w φ hφ, fun τ i j => hE τ i j φ hφ, fun Y => hL Y φ hφ⟩
