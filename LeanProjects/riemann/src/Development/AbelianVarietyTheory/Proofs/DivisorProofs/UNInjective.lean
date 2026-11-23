import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviFubini

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev parB {a b n : ℕ} (h : a + b = n) (w : Pl E) : Subgroup (GLw n w) :=
  GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))

def levH {a b n : ℕ} (h : a + b = n) (w : Pl E) : parB h w →* GLw a w × GLw b w :=
  (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom.comp
    (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)))

theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blk h w m X ∈ parB h w := by
  rw [GlobalTheory.SmGL.mem_parab_two]
  intro j i
  rw [CtLevel.blk_val]
  show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
    (CtLevel.blkEq h (Sum.inr j)) (CtLevel.blkEq h (Sum.inl i)) = 0
  simp

theorem blk_mul_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m m' : GLw a w × GLw b w)
    (X X' : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m X * blk h w m' X' = blk h w (m * m') (X' + (m'.1⁻¹).val * X * m'.2.val) := by
  ext1
  rw [Units.val_mul, CtLevel.blk_val, CtLevel.blk_val, CtLevel.blk_val, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, fromBlocks_multiply]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
    Matrix.mul_add]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (m'.1.val) ((m'.1⁻¹ : GLw a w).val), Units.mul_inv, Matrix.one_mul]

theorem blk_one_zero {a b n : ℕ} (h : a + b = n) (w : Pl E) : blk h w 1 0 = 1 := by
  ext1
  rw [CtLevel.blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Units.val_one, Matrix.mul_zero, fromBlocks_one,
    reindex_apply, submatrix_one_equiv]
  rfl

def sM {a b n : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* parB h w where
  toFun m := ⟨blk h w m 0, blk_mem h w m 0⟩
  map_one' := Subtype.ext (blk_one_zero h w)
  map_mul' m m' := Subtype.ext (by simp [blk_mul_blk])

def uN {a b n : ℕ} (h : a + b = n) (w : Pl E) : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* parB h w where
  toFun X := ⟨blk h w 1 (Multiplicative.toAdd X), blk_mem h w 1 _⟩
  map_one' := Subtype.ext (by simpa using blk_one_zero h w)
  map_mul' X Y := Subtype.ext (by simp [blk_mul_blk, add_comm])

theorem sM_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    (sM h w m : GLw n w) = blk h w m 0 := rfl

theorem uN_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    (uN h w X : GLw n w) = blk h w 1 (Multiplicative.toAdd X) := rfl

theorem sM_mul_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    ((sM h w m * uN h w X : parB h w) : GLw n w) = blk h w m (Multiplicative.toAdd X) := by
  rw [Subgroup.coe_mul, sM_val, uN_val, blk_mul_blk]
  simp

theorem levH_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : levH h w ⟨blk h w m X, blk_mem h w m X⟩ = m := by
  have key : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ x :
        GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j = ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m x : GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [GlobalTheory.SmGL.leviProj_apply, CtLevel.blk_val]
    cases x
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
  have : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ =
      GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    funext x; exact Units.ext (Matrix.ext fun i j => key x i j)
  simp only [levH, MonoidHom.coe_comp, Function.comp_apply, this]
  simp

theorem levH_sM {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) : levH h w (sM h w m) = m :=
  levH_blk h w m 0

theorem levH_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    levH h w (uN h w X) = 1 :=
  levH_blk h w 1 _

theorem uN_injective {a b n : ℕ} (h : a + b = n) (w : Pl E) : Function.Injective (uN h w) := by
  intro X Y hXY
  have h1 := congrArg (fun p : parB h w => ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hXY
  simp only [uN_val, CtLevel.blk_val] at h1
  have h2 := congrArg (fun M => M.toBlocks₁₂) ((reindex (CtLevel.blkEq h) (CtLevel.blkEq h)).injective h1)
  simpa using h2

theorem exists_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (p : parB h w) (hp : levH h w p = 1) :
    ∃ X, uN h w X = p := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p = 1 := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) hp
    simpa [levH] using this
  have hd : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, i⟩) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, j⟩) =
        (1 : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [← GlobalTheory.SmGL.leviProj_apply, hl]
    rfl
  have h0 := (GlobalTheory.SmGL.mem_parab_two _).1 p.2
  refine ⟨Multiplicative.ofAdd
    ((((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).submatrix (CtLevel.blkEq h) (CtLevel.blkEq h)).toBlocks₁₂),
    Subtype.ext (Units.ext ?_)⟩
  rw [uN_val, CtLevel.blk_val]
  refine Matrix.ext fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [fromBlocks_apply₁₁]
    exact (hd false i j).symm
  · simp [toBlocks₁₂]
  · rw [fromBlocks_apply₂₁]
    exact (h0 i j).symm
  · rw [fromBlocks_apply₂₂]
    exact (hd true i j).symm

end GlobalTheory.LeviFubini
