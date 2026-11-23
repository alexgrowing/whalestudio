import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory

theorem matrix_mem_span_incM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    (u : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)),
    u ∈ Submodule.span (AF F) (Set.range (incM F : Matrix (Fin m) (Fin n) E → Matrix (Fin m) (Fin n) (AF F ⊗[F] E))) := by
  intro F E _ _ _ _ _ m n u
  classical
  rw [Matrix.matrix_eq_sum_single u]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  generalize u i j = a
  induction a using TensorProduct.induction_on with
  | zero => rw [Matrix.single_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [Matrix.single_add]; exact Submodule.add_mem _ hx hy
  | tmul a e =>
    have h : Matrix.single i j (a ⊗ₜ[F] e) = a • incM F (Matrix.single i j e) := by
      ext k l
      simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single, Matrix.of_apply]
      split_ifs
      · change _ = a • ((1 : AF F) ⊗ₜ[F] e)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · simp
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory
