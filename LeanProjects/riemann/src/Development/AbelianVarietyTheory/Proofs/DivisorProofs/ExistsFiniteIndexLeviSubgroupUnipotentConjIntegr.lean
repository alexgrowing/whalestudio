import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentConjLeviEqBlockUpperTwistedSylvester
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc.ConjStab

variable {E : Type} [Field E] [NumberField E]

def dgHom {n a b : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* GLw n w where
  toFun k := blk h w k 0
  map_one' := by
    ext : 1
    rw [LeviBlockConjugation.blk_val]
    simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.mul_zero, Matrix.fromBlocks_one, Matrix.reindex_apply]
    exact Matrix.submatrix_one_equiv _
  map_mul' k k' := by
    ext : 1
    simp only [Units.val_mul, LeviBlockConjugation.blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul]
    simp

theorem continuous_dgHom {n a b : ℕ} (h : a + b = n) (w : Pl E) : Continuous (dgHom (E := E) h w) := by
  rw [Units.continuous_iff]
  constructor
  · have e : (fun k : GLw a w × GLw b w => (dgHom h w k).val) = fun k =>
        Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
          (Matrix.fromBlocks k.1.val (k.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 k.2.val) := by
      funext k; exact LeviBlockConjugation.blk_val h w k 0
    change Continuous fun k : GLw a w × GLw b w => (dgHom h w k).val
    rw [e]
    exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst)
      ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_const) continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · have e : (fun k : GLw a w × GLw b w => ((dgHom h w k)⁻¹).val) = fun k =>
        Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
          (Matrix.fromBlocks (k.1⁻¹).val ((k.1⁻¹).val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 (k.2⁻¹).val) := by
      funext k; rw [← map_inv]; exact LeviBlockConjugation.blk_val h w k⁻¹ 0
    change Continuous fun k : GLw a w × GLw b w => ((dgHom h w k)⁻¹).val
    rw [e]
    exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst)
      ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul continuous_const) continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

def conjLevi {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GLw a w × GLw b w →* GLw n w :=
  (MulAut.conj (blk h w 1 X)⁻¹).toMonoidHom.comp (dgHom h w)

theorem conjLevi_apply {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (k : GLw a w × GLw b w) : conjLevi h w X k = (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X := by
  simp [conjLevi, dgHom, MulAut.conj_apply]

theorem continuous_conjLevi {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    Continuous (conjLevi h w X) := by
  have e : (conjLevi h w X : GLw a w × GLw b w → GLw n w) = fun k => (blk h w 1 X)⁻¹ * dgHom h w k * blk h w 1 X := by
    funext k; rw [conjLevi_apply]; rfl
  rw [e]
  exact (continuous_const.mul (continuous_dgHom h w)).mul continuous_const

end GlobalTheory.LeviDesc.ConjStab

open GlobalTheory.LeviDesc.ConjStab in

theorem GlobalTheory.LeviDesc.ConjStab.exists_stab : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), ∃ U : Subgroup (GLw a w × GLw b w),
    U ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) ∧ U.relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0 ∧
    ∀ k ∈ U, (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X ∈ GlobalTheory.LFun.KGL w n := by
  intro E _ _ n a b h w X
  set P : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)
  set C : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w n).comap (conjLevi h w X)
  refine ⟨P ⊓ C, inf_le_left, ?_, fun k hk => ?_⟩
  · rw [Subgroup.inf_relIndex_left]
    have hP : IsCompact (P : Set (GLw a w × GLw b w)) := by
      simp only [P, Subgroup.coe_prod]
      exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
    have hC : IsOpen (C : Set (GLw a w × GLw b w)) :=
      (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.preimage (continuous_conjLevi h w X)
    haveI : CompactSpace P := isCompact_iff_compactSpace.mp hP
    haveI : Finite (P ⧸ C.subgroupOf P) :=
      Subgroup.quotient_finite_of_isOpen _ (hC.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  · have := (Subgroup.mem_inf.1 hk).2
    rw [Subgroup.mem_comap, conjLevi_apply] at this
    exact this
