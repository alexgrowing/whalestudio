import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviFubini.IntPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_GLint_of_entries {L : Type} [Field L] {k : ℕ} (O : Subring L) (g : GL (Fin k) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin k) O := by
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem entries_of_mem {L : Type} [Field L] {k : ℕ} {O : Subring L} {A : GL (Fin k) L}
    (hA : A ∈ Formalism.UG.GLint (Fin k) O) (i j : Fin k) : A.val i j ∈ O ∧ (A⁻¹).val i j ∈ O := by
  obtain ⟨y, rfl⟩ := hA
  rw [← map_inv]
  exact ⟨(y.val i j).2, ((y⁻¹).val i j).2⟩

theorem blk_entries {a b n : ℕ} (h : a + b = n) (w : Pl E) (O : Subring (w.adicCompletion E))
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (h1 : ∀ i j, m.1.val i j ∈ O) (h2 : ∀ i j, m.2.val i j ∈ O) (hX : ∀ i j, X i j ∈ O) (i j : Fin n) :
    (blk h w m X).val i j ∈ O := by
  rw [CtLevel.blk_val]
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [fromBlocks_apply₁₁]; exact h1 i j
  · rw [fromBlocks_apply₁₂, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h1 i k) (hX k j)
  · rw [fromBlocks_apply₂₁]; exact Subring.zero_mem _
  · rw [fromBlocks_apply₂₂]; exact h2 i j

theorem blk_one_corner {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (i : Fin a) (j : Fin b) : (blk h w 1 X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j)) = X i j := by
  rw [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    fromBlocks_apply₁₂]
  simp

theorem mem_intMat_iff {a b : ℕ} (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    X ∈ intMat a b w ↔ ∀ i j, Multiplicative.toAdd X i j ∈ Ov E w := by
  let S : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :=
    { carrier := {X | ∀ i j, Multiplicative.toAdd X i j ∈ Ov E w}
      mul_mem' := fun {x y} hx hy i j => by
        show (Multiplicative.toAdd x + Multiplicative.toAdd y) i j ∈ Ov E w
        exact Subring.add_mem _ (hx i j) (hy i j)
      one_mem' := fun i j => by
        show (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E)) i j ∈ Ov E w
        exact Subring.zero_mem _
      inv_mem' := fun {x} hx i j => by
        show (-Multiplicative.toAdd x) i j ∈ Ov E w
        exact Subring.neg_mem _ (hx i j) }
  have hv : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  constructor
  · intro hX
    refine (Subgroup.closure_le S).2 ?_ hX
    intro Y hY i j
    exact (hv _).1 (hY i j)
  · intro hX
    exact Subgroup.subset_closure fun i j => (hv _).2 (hX i j)

theorem intPts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E),
    ((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) = intMat a b w ∧
    ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).map (GlobalTheory.LeviFubini.sM h w) ≤
      (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w) := by
  intro E _ _ _ a b n h w
  constructor
  · ext X
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, uN_val, mem_intMat_iff]
    constructor
    · intro hK i j
      have := (entries_of_mem hK (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))).1
      rwa [blk_one_corner] at this
    · intro hX
      have hO1 : ∀ (k : ℕ) (i j : Fin k), ((1 : GLw k w) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) i j ∈ Ov E w := by
        intro k i j
        rw [Units.val_one, Matrix.one_apply]
        split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _
      refine mem_GLint_of_entries _ _ (blk_entries h w _ 1 _ (hO1 a) (hO1 b) hX) ?_
      rw [CtLevel.blk_inv]
      refine blk_entries h w _ _ _ (by simpa using hO1 a) (by simpa using hO1 b) ?_
      intro i j
      simp only [Prod.fst_one, Prod.snd_one, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.neg_apply]
      exact Subring.neg_mem _ (hX i j)
  · rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf, sM_val]
    have e1 := fun i j => entries_of_mem hm1 i j
    have e2 := fun i j => entries_of_mem hm2 i j
    refine mem_GLint_of_entries _ _ (blk_entries h w _ m 0 (fun i j => (e1 i j).1) (fun i j => (e2 i j).1)
      (fun i j => Subring.zero_mem _)) ?_
    rw [CtLevel.blk_inv]
    refine blk_entries h w _ _ _ (fun i j => (e1 i j).2) (fun i j => (e2 i j).2) ?_
    intro i j
    simp only [Matrix.mul_zero, Matrix.zero_mul, neg_zero, Matrix.zero_apply]
    exact Subring.zero_mem _

end GlobalTheory.LeviFubini.IntPts
