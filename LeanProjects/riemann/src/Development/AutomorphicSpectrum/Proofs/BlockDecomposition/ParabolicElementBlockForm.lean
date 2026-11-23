import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ParabBlock

theorem parab_eq_blk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (p : parab (w.adicCompletion E) (two (stdSum h))), ∃ X, (p : GLw n w) = GlobalTheory.BCT.blk h w ((leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm (leviProj (w.adicCompletion E) (two (stdSum h)) p)) X := by
  intro E _ _ _ n a b h w p
  obtain ⟨m, hm⟩ : ∃ m, m = (leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (leviProj (w.adicCompletion E) (two (stdSum h)) p) := ⟨_, rfl⟩
  have h1 : ∀ i j, (m.1 : Matrix _ _ (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) := by
    intro i j; rw [hm]; rfl
  have h2 : ∀ i j, (m.2 : Matrix _ _ (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) := by
    intro i j; rw [hm]; rfl
  have h0 : ∀ (i : Fin b) (j : Fin a),
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
    intro i j
    exact mem_parab_iff.1 p.2 true false i j (by decide)
  rw [← hm]
  let B : Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun i j =>
    ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j))
  refine ⟨(m.1⁻¹).val * B, ?_⟩
  have hM : Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * ((m.1⁻¹).val * B)) 0 m.2.val) =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) := by
    have hc : m.1.val * ((m.1⁻¹).val * B) = B := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [hc]
    refine Matrix.ext fun i j => ?_
    obtain ⟨i, rfl⟩ := (stdSum h).surjective i
    obtain ⟨j, rfl⟩ := (stdSum h).surjective j
    have hs : finSumFinEquiv.trans (finCongr h) = stdSum h := rfl
    rw [hs]
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · exact h1 i j
    · rfl
    · exact (h0 i j).symm
    · exact h2 i j
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * ((m.1⁻¹).val * B)) 0 m.2.val)) := by
    rw [hM]; exact (p : GLw n w).isUnit
  unfold GlobalTheory.BCT.blk
  simp only
  rw [dif_pos hU]
  exact Units.ext (by rw [IsUnit.unit_spec, hM])

end GlobalTheory.CompanionTheory.ParabBlock
