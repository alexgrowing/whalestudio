import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlace
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.GL3BlockMatrixLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_zero_eq {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    blk h w m 0 = CtLevel.dgM h w m := by
  ext1
  rw [CtLevel.blk_val, CtLevel.dgM_val, CtLevel.dgMat, Matrix.mul_zero]

theorem continuous_dgM {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) := by
  have e : (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) = fun k =>
      ((CtLevel.dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) k.1 *
        ((CtLevel.dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) k.2 := by
    funext k
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, ← map_mul]
    simp
  rw [e]
  exact ((CtLevel.continuous_dgM_inl h w).comp continuous_fst).mul
    ((CtLevel.continuous_dgM_inr h w).comp continuous_snd)

theorem dgM_entries {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) :
    (∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = k.1.val i j) ∧
      ∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = k.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply] <;> simp

theorem blocks_mem_KGL {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w)
    (hk : CtLevel.dgM h w k ∈ GlobalTheory.LFun.KGL w n) : k.1 ∈ GlobalTheory.LFun.KGL w a ∧ k.2 ∈ GlobalTheory.LFun.KGL w b := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [← map_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k⁻¹).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k⁻¹).2] at this

theorem constant_term_bi_invariant {a b n : ℕ} (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w))
    (hKK : K' ≤ GlobalTheory.LFun.KGL w n) (hN : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (f : GLw n w → ℂ) (hf : ∀ k₁ ∈ K', ∀ k₂ ∈ K', ∀ g, f (k₁ * g * k₂) = f g)
    (x y : GLw n w) (hx : x ∈ GlobalTheory.LFun.KGL w n) (hy : y ∈ GlobalTheory.LFun.KGL w n)
    (k₁ k₂ : GLw a w × GLw b w) (hk₁ : k₁ ∈ leviOf h w K') (hk₂ : k₂ ∈ leviOf h w K')
    (m : GLw a w × GLw b w) : phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  have hd₁ : CtLevel.dgM h w k₁ ∈ K' := by
    have : blk h w k₁ 0 ∈ K' := hk₁
    rwa [blk_zero_eq] at this
  have hd₂ : CtLevel.dgM h w k₂ ∈ K' := by
    have : blk h w k₂ 0 ∈ K' := hk₂
    rwa [blk_zero_eq] at this
  obtain ⟨h11, h12⟩ := blocks_mem_KGL h w k₁ (hKK hd₁)
  obtain ⟨h21, h22⟩ := blocks_mem_KGL h w k₂ (hKK hd₂)
  have hab : absHalf w ((k₁ * m * k₂).1.val.det ^ b / (k₁ * m * k₂).2.val.det ^ a) =
      absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
    rw [(absHalf_blockDet_KGL_invariant E a b w (k₁ * m) k₂ h21 h22).2]
    exact (absHalf_blockDet_KGL_invariant E a b w m k₁ h11 h12).1
  have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (x⁻¹ * blk h w (k₁ * m * k₂) (Multiplicative.toAdd X) * y)) =
      fun X => (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
        (Multiplicative.ofAdd (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val)) := by
    funext X
    rw [(CtLevel.blk_mul_dgM E a b n h w (k₁ * m) k₂ _).2, (CtLevel.blk_mul_dgM E a b n h w m k₁ _).1]
    have hc₁ : x⁻¹ * CtLevel.dgM h w k₁ * x ∈ K' := by
      simpa using hN x⁻¹ (inv_mem hx) _ hd₁
    have hc₂ : y⁻¹ * CtLevel.dgM h w k₂ * y ∈ K' := by
      simpa using hN y⁻¹ (inv_mem hy) _ hd₂
    have e2 : x⁻¹ * (CtLevel.dgM h w k₁ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) *
        CtLevel.dgM h w k₂) * y =
        (x⁻¹ * CtLevel.dgM h w k₁ * x) *
          (x⁻¹ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) * y) *
          (y⁻¹ * CtLevel.dgM h w k₂ * y) := by group
    rw [e2, hf _ hc₁ _ hc₂]
    rfl
  unfold phi3
  rw [hab, e, HintInv.hint_intMat_mul_mul E a b w (fun Y => f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
    k₂.1 k₂.2⁻¹ h21 (inv_mem h22)]

theorem constant_term_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (x y : GLw n w)
    (m : GLw a w × GLw b w) (hm : phi3 h w f x y m ≠ 0) :
    ∃ X, blk h w m X ∈ ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} := by
  obtain ⟨X, hX⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ (right_ne_zero_of_mul hm)
  refine ⟨Multiplicative.toAdd X, ?_⟩
  have e : blk h w m (Multiplicative.toAdd X) =
      x * (x⁻¹ * blk h w m (Multiplicative.toAdd X) * y) * y⁻¹ := by group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul rfl (subset_tsupport _ hX)) rfl

theorem constant_term_compact_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ)
    (hf : HasCompactSupport f) (x y : GLw n w) : HasCompactSupport (phi3 h w f x y) := by
  set C : Set (GLw n w) := ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} with hCdef
  have hC : IsCompact C := (isCompact_singleton.mul hf).mul isCompact_singleton
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((CtLevel.blkTL h g.val, MulOpposite.op (CtLevel.blkTL h (g⁻¹).val)),
      (CtLevel.blkBR h g.val, MulOpposite.op (CtLevel.blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((CtLevel.continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((CtLevel.continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, CtLevel.blk_inv, CtLevel.blkTL_blk, CtLevel.blkBR_blk,
      Prod.fst_inv, Prod.snd_inv]
  have hT : IsCompact (ψ '' C) := hC.image hψ
  refine HasCompactSupport.intro' (hι.isCompact_preimage hT) (hT.isClosed.preimage hι.continuous) ?_
  intro m hm
  by_contra hne
  obtain ⟨X, hX⟩ := constant_term_support h w f x y m hne
  exact hm ⟨blk h w m X, hX, (hιψ m X).symm⟩

theorem constant_term_locally_constant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f : GLw n w → ℂ, IsHk K' f → ∀ x ∈ X, ∀ y ∈ X, IsLocallyConstant (phi3 h w f x y) ∧ HasCompactSupport (phi3 h w f x y) ∧ ∀ k₁ ∈ leviOf h w K', ∀ k₂ ∈ leviOf h w K', ∀ m, phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  intro E _ _ _ n a b h w K' hKo hKK hN X hXK _ f hf x hx y hy
  have hbi := constant_term_bi_invariant h w K' hKK hN f hf.2.2.2 x y (hXK x hx) (hXK y hy)
  refine ⟨?_, constant_term_compact_support h w f hf.2.2.1 x y, fun k₁ h₁ k₂ h₂ m => hbi k₁ k₂ h₁ h₂ m⟩
  have hL : IsOpen (leviOf h w K') := by
    have e : leviOf h w K' = (CtLevel.dgM h w) ⁻¹' (K' : Set (GLw n w)) := by
      ext m
      simp only [leviOf, Set.mem_setOf_eq, Set.mem_preimage, blk_zero_eq, SetLike.mem_coe]
    rw [e]
    exact hKo.preimage (continuous_dgM h w)
  have h1 : (1 : GLw a w × GLw b w) ∈ leviOf h w K' := by
    show blk h w 1 0 ∈ K'
    rw [blk_zero_eq, map_one]
    exact K'.one_mem
  rw [IsLocallyConstant.iff_exists_open]
  intro m
  refine ⟨(fun m' => m⁻¹ * m') ⁻¹' leviOf h w K', hL.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using h1
  · intro m' hm'
    have := hbi 1 (m⁻¹ * m') h1 hm' m
    simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.GL3BlockMatrixLocal
