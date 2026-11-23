import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv.UnipInv

theorem mem_unip_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ)
    (W : Spc F E d) (H' : Plane E d d₁) (g : UA σ W.J), g ∈ unip σ W H' →
    mat g *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z : Fin d₁ → AE F E, ∃ a : AE F E, mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x := by
  intro F E _ _ _ _ _ σ d d₁ W H' g hg
  unfold unip at hg
  induction hg using Subgroup.closure_induction with
  | mem u hu => exact hu
  | one =>
    refine ⟨by rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec], fun z => ⟨0, ?_⟩⟩
    rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec, zero_smul, add_zero]
  | mul u w _ _ hu hw =>
    refine ⟨by rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hw.1, hu.1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hw.2 z
    obtain ⟨a', ha'⟩ := hu.2 z
    refine ⟨a' + a, ?_⟩
    rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, ha', hu.1, add_smul,
      add_assoc]
  | inv u _ hu =>
    have hinv : mat u⁻¹ * mat u = 1 := by rw [← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one]
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu.1]
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu.2 z
    refine ⟨-a, ?_⟩
    have h1 : incM F H'.ι *ᵥ z = mat u *ᵥ (incM F H'.ι *ᵥ z) - a • incV F H'.x := by rw [ha, add_sub_cancel_right]
    conv_lhs => rw [h1]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_smul, hx, neg_smul,
      sub_eq_add_neg]

end GlobalTheory.ThK.LemF.QuotInv.UnipInv
