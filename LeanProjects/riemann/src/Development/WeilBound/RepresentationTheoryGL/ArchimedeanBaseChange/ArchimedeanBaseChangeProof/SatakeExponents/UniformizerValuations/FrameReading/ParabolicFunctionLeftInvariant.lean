import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail.B

theorem hint_mul_right_comm {H : Type} [CommGroup H] (K : Subgroup H) (u : H → ℂ) (t : H) :
    hint K (fun X => u (X * t)) = hint K u := by
  have hr : rStab (fun X => u (X * t)) = rStab u := by
    ext k
    show (∀ x, u (x * k * t) = u (x * t)) ↔ ∀ x, u (x * k) = u x
    constructor
    · intro hk x
      have := hk (x * t⁻¹)
      rwa [mul_right_comm (x * t⁻¹) k t, inv_mul_cancel_right] at this
    · intro hk x
      rw [mul_right_comm x k t, hk]
  unfold hint
  rw [hr]
  congr 1
  set S := rStab u ⊓ K with hS
  have key : ∀ q : H ⧸ S, u ((MulAction.toPerm t q : H ⧸ S).out) = u (q.out * t) := by
    intro q
    have h1 : (MulAction.toPerm t q : H ⧸ S) = ((t * q.out : H) : H ⧸ S) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (t * q.out)
    rw [h1, hs, (Subgroup.mem_inf.1 s.2).1, mul_comm]
  calc ∑ᶠ q : H ⧸ S, u (q.out * t) = ∑ᶠ q : H ⧸ S, u ((MulAction.toPerm t q : H ⧸ S).out) :=
        finsum_congr fun q => (key q).symm
    _ = ∑ᶠ q : H ⧸ S, u q.out := finsum_comp_equiv (MulAction.toPerm t) (f := fun q : H ⧸ S => u q.out)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_mul {n a b : ℕ} (h : a + b = n) (w : Pl E) (m m' : GLw a w × GLw b w)
    (X X' : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m X * blk h w m' X' = blk h w (m * m') (X' + (m'.1⁻¹).val * X * m'.2.val) := by
  apply Units.ext
  rw [Units.val_mul, CtLevel.blk_val, CtLevel.blk_val, CtLevel.blk_val, reindex_apply, reindex_apply,
    reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  have e : (m'.1.val) * (m'.1⁻¹).val = 1 := Units.mul_inv _
  have key : m.1.val * (m'.1.val * X') + m.1.val * X * m'.2.val =
      (m * m').1.val * (X' + (m'.1⁻¹).val * X * m'.2.val) := by
    rw [Prod.fst_mul, Units.val_mul]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc m'.1.val (m'.1⁻¹).val, e, Matrix.one_mul]
  rw [key]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Prod.fst_mul, Prod.snd_mul, Units.val_mul]

theorem blk_entries {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = m.1.val i j) ∧
      ∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = m.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] <;> rfl

theorem blocks_of_blk_mem {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (hk : blk h w m X ∈ GlobalTheory.LFun.KGL w n) :
    m.1 ∈ GlobalTheory.LFun.KGL w a ∧ m.2 ∈ GlobalTheory.LFun.KGL w b := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [CtLevel.blk_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w m X).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w _ _).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w m X).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w _ _).2] at this

theorem parabolic_function_left_invariant {n a b : ℕ} (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (f : GLw n w → ℂ)
    (hf : ∀ k ∈ K', ∀ g, f (k * g) = f g) (x y : GLw n w) (mq : GLw a w × GLw b w) (hmq1 : mq.1 ∈ GlobalTheory.LFun.KGL w a)
    (hmq2 : mq.2 ∈ GlobalTheory.LFun.KGL w b) (Z : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (k' : GLw n w) (hk' : k' ∈ K')
    (m : GLw a w × GLw b w) : phi3 h w f (blk h w mq Z * x * k') y m = phi3 h w f x y (mq⁻¹ * m) := by
  have hab : absHalf w ((mq⁻¹ * m).1.val.det ^ b / (mq⁻¹ * m).2.val.det ^ a) =
      absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) :=
    (absHalf_blockDet_KGL_invariant E a b w m mq⁻¹ (inv_mem hmq1) (inv_mem hmq2)).1
  set T : Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
    (m.1⁻¹).val * (-(mq.1.val * Z * (mq.2⁻¹).val)) * m.2.val with hT
  have hstep : ∀ X : Matrix (Fin a) (Fin b) (w.adicCompletion E),
      f ((blk h w mq Z * x * k')⁻¹ * blk h w m X * y) = f (x⁻¹ * blk h w (mq⁻¹ * m) (X + T) * y) := by
    intro X
    have e1 : (blk h w mq Z * x * k')⁻¹ * blk h w m X * y =
        k'⁻¹ * (x⁻¹ * ((blk h w mq Z)⁻¹ * blk h w m X) * y) := by group
    rw [e1, hf _ (inv_mem hk'), CtLevel.blk_inv, blk_mul]
  unfold phi3
  rw [hab]
  congr 1
  simp_rw [hstep]
  exact hint_mul_right_comm (intMat a b w)
    (fun Y => f (x⁻¹ * blk h w (mq⁻¹ * m) (Multiplicative.toAdd Y) * y)) (Multiplicative.ofAdd T)

theorem parab_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (p : GLw n w)
    (hp : p ∈ GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))) :
    ∃ Z, p = blk h w ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨p, hp⟩)) Z := by
  set A := (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
    (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨p, hp⟩) with hA
  refine ⟨(A.1⁻¹).val * (Matrix.of fun i j => p.val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))), ?_⟩
  apply Units.ext
  rw [CtLevel.blk_val, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  refine Matrix.ext fun i j => ?_
  obtain ⟨s, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨t, rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases s with s | s <;> rcases t with t | t
  · rfl
  · rfl
  · have h1 : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) (CtLevel.blkEq h (Sum.inr s)) = true :=
      GlobalTheory.SmGL.blk_apply (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) true s
    have h2 : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) (CtLevel.blkEq h (Sum.inl t)) = false :=
      GlobalTheory.SmGL.blk_apply (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) false t
    exact GlobalTheory.SmGL.mem_parab.1 hp (CtLevel.blkEq h (Sum.inr s)) (CtLevel.blkEq h (Sum.inl t))
      (by rw [h1, h2]; decide)
  · rfl

theorem deltaHalf_int {a b : ℕ} (w : Pl E) (m : GLw a w × GLw b w) (h1 : m.1 ∈ GlobalTheory.LFun.KGL w a)
    (h2 : m.2 ∈ GlobalTheory.LFun.KGL w b) :
    (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b))
      (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) = 1 := by
  have hg : ∀ x : Bool, (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) x ∈
      GlobalTheory.SplitWeil.KO (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) := by
    intro x
    cases x
    · show m.1 ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a)
      rw [← GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]; exact h1
    · show m.2 ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin b)
      rw [← GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]; exact h2
  rw [GlobalTheory.SatInd.deltaHalf_eq_one hg, Units.val_one]

end PositivityTheory.Rg.BcB.F.Tail.B

end
