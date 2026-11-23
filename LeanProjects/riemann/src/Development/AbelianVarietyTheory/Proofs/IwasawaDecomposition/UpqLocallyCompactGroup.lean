import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.UpqTopology

variable {P Q : ℕ}

theorem jpq_sq : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem left_inv {u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ}
    (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) : Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, h, jpq_sq]

theorem mat_unitary (b : UpqT P Q) : (UpqT.mat b)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat b = Formalism.UG.Jpq P Q := b.2

theorem continuous_mat : Continuous (UpqT.mat (P := P) (Q := Q)) :=
  Units.continuous_val.comp continuous_subtype_val

theorem range_mat : Set.range (UpqT.mat (P := P) (Q := Q)) =
    {u | uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q} := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact mat_unitary b
  · intro h
    exact ⟨(⟨⟨u, Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q, mul_eq_one_comm.1 (left_inv h), left_inv h⟩, h⟩ :
      Formalism.UG.Upq P Q), rfl⟩

theorem isInducing_mat : IsInducing (UpqT.mat (P := P) (Q := Q)) := by
  let f : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ × (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᵐᵒᵖ :=
    fun g => (g, MulOpposite.op (Formalism.UG.Jpq P Q * gᴴ * Formalism.UG.Jpq P Q))
  have hf : Continuous f :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : f ∘ UpqT.mat =
      Units.embedProduct _ ∘ (Subtype.val : Formalism.UG.Upq P Q → GL (Fin P ⊕ Fin Q) ℂ) := by
    funext g
    refine Prod.ext rfl (congrArg MulOpposite.op ?_)
    exact (Units.inv_eq_of_mul_eq_one_left (left_inv (mat_unitary g))).symm
  refine IsInducing.of_comp continuous_mat hf ?_
  rw [hcomp]
  exact Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal

theorem isClosedEmbedding_mat : IsClosedEmbedding (UpqT.mat (P := P) (Q := Q)) := by
  refine ⟨⟨isInducing_mat, fun _ _ h => Subtype.ext (Units.ext h)⟩, ?_⟩
  rw [range_mat]
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem upq_lcsc : ∀ P Q : ℕ, IsTopologicalGroup (UpqT P Q) ∧ T2Space (UpqT P Q) ∧
    LocallyCompactSpace (UpqT P Q) ∧ SecondCountableTopology (UpqT P Q) ∧ BorelSpace (UpqT P Q) ∧
    Topology.IsClosedEmbedding (UpqT.mat : UpqT P Q → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
  intro P Q
  have : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact ⟨inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q)), isClosedEmbedding_mat.isEmbedding.t2Space,
    isClosedEmbedding_mat.locallyCompactSpace, isClosedEmbedding_mat.isEmbedding.secondCountableTopology,
    ⟨rfl⟩, isClosedEmbedding_mat⟩

end GlobalTheory.UpqTopology
