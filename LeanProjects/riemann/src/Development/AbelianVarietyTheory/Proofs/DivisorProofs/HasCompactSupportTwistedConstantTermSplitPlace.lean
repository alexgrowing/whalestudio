import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_ne_zero_of_hint_ne_zero {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) (hu : hint K u ≠ 0) :
    ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hu (by simp [hint, hc])

theorem exists_ne_zero_of_avg_ne_zero {H : Type} [Group H] (u : H → ℂ) (hu : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hu (by simp [avg, hc])

theorem blk_inv {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X)⁻¹ = blk h w m⁻¹ (-(m.1.val * X * (m.2⁻¹).val)) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, blk_val, blk_val, Units.val_one, reindex_apply, reindex_apply, submatrix_mul_equiv,
    fromBlocks_multiply]
  have e1 : m.1.val * (m.1⁻¹).val = 1 := Units.mul_inv _
  have e2 : m.2.val * (m.2⁻¹).val = 1 := Units.mul_inv _
  simp only [Prod.fst_inv, Prod.snd_inv, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  rw [e1, e2, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc m.1.val, add_comm]
  simp [fromBlocks_one]
  exact submatrix_one_equiv (blkEq h).symm

end GlobalTheory.BCT.CtLevel

open scoped Pointwise

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def blkTL {R : Type} {a b n : ℕ} (h : a + b = n) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin a) (Fin a) R :=
  (reindex (blkEq h).symm (blkEq h).symm g).toBlocks₁₁

def blkBR {R : Type} {a b n : ℕ} (h : a + b = n) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin b) (Fin b) R :=
  (reindex (blkEq h).symm (blkEq h).symm g).toBlocks₂₂

theorem blkTL_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blkTL h (blk h w m X).val = m.1.val := by
  rw [blkTL, blk_val, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₁₁]

theorem blkBR_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blkBR h (blk h w m X).val = m.2.val := by
  rw [blkBR, blk_val, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₂₂]

theorem continuous_blkTL {R : Type} [TopologicalSpace R] {a b n : ℕ} (h : a + b = n) :
    Continuous (blkTL (R := R) h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blkTL, toBlocks₁₁, reindex_apply, submatrix_apply, of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_blkBR {R : Type} [TopologicalSpace R] {a b n : ℕ} (h : a + b = n) :
    Continuous (blkBR (R := R) h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blkBR, toBlocks₂₂, reindex_apply, submatrix_apply, of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem hasCompactSupport_ctMu_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w → HasCompactSupport f →
    HasCompactSupport (ctMu h w μ f) := by
  intro E _ _ _ a b n h w μ f hw hf
  have hUL : ∀ y : GLw n w, y ∈ UL n w := fun y => by rw [UL, if_pos hw]; trivial
  set S : Set (GLw n w) := Subtype.val '' tsupport f with hSdef
  have hS : IsCompact S := hf.image continuous_subtype_val
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  set C : Set (GLw n w) := (GlobalTheory.LFun.KGL w n : Set (GLw n w)) * S * (GlobalTheory.LFun.KGL w n : Set (GLw n w)) with hCdef
  have hC : IsCompact C := (hK.mul hS).mul hK
  have hmem : ∀ m, ctMu h w μ f m ≠ 0 → ∃ X, blk h w m X ∈ C := by
    intro m hm
    have h1 := right_ne_zero_of_mul (right_ne_zero_of_mul hm)
    obtain ⟨X, hX⟩ := exists_ne_zero_of_hint_ne_zero _ _ h1
    obtain ⟨k, hk⟩ := exists_ne_zero_of_avg_ne_zero _ hX
    refine ⟨Multiplicative.toAdd X, ?_⟩
    set y := (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k with hy
    have hyS : y ∈ S := by
      refine ⟨⟨y, hUL y⟩, subset_tsupport _ ?_, rfl⟩
      have : toSub (UL n w) y = ⟨y, hUL y⟩ := by rw [toSub, dif_pos (hUL y)]
      simpa [this] using hk
    have e : blk h w m (Multiplicative.toAdd X) = (k : GLw n w) * y * (k : GLw n w)⁻¹ := by
      rw [hy]; group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul k.2 hyS) (inv_mem k.2)
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((blkTL h g.val, MulOpposite.op (blkTL h (g⁻¹).val)), (blkBR h g.val, MulOpposite.op (blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, blk_inv, blkTL_blk, blkBR_blk, Prod.fst_inv, Prod.snd_inv]
  have hT : IsCompact (ψ '' C) := hC.image hψ
  refine HasCompactSupport.intro' (hι.isCompact_preimage hT) (hT.isClosed.preimage hι.continuous) ?_
  intro m hm
  by_contra hne
  obtain ⟨X, hX⟩ := hmem m hne
  exact hm ⟨blk h w m X, hX, (hιψ m X).symm⟩

end GlobalTheory.BCT.CtLevel
