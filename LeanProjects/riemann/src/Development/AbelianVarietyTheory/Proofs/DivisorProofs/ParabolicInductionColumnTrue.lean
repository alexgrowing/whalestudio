import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerEquivUpperSwap
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SmGL.RowOneCell Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.RowOneCell

theorem colTwo_parInd_equiv_prod₂ : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ), Nonempty ((parInd (colPart u v true) (colRep χ₁ χ₂ u v true)).Equiv
      (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (1 / 2))))) := by
  intro k _ _ _ _ χ₁ χ₂ u v
  have hP : parab k (colPart u v true) = parab k (two (stdSum (rfl : u + v = u + v))) := by
    ext g; exact Iff.rfl
  refine GlobalTheory.SmGL.SwapBlocks.smInd_equiv_of_eq hP _ _ fun g hg hg' => ?_
  have hA : GeneralLinearGroup.det (leviProj k (colPart u v true) ⟨g, hg⟩ false) =
      GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨g, hg'⟩ false) := by
    congr 1
  have hD : GeneralLinearGroup.det (leviProj k (colPart u v true) ⟨g, hg⟩ true) =
      GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨g, hg'⟩ true) := by
    congr 1
  have cf : ∀ (n : ℕ) (inst : Fintype (Fin n)), @Fintype.card (Fin n) inst = n := fun n _ => by
    convert Fintype.card_fin n
  have e1 : modExp (fun i => Fin (sz u v i true)) true = -(u : ℤ) := by
    unfold modExp; simp only [Finset.sum_filter, Fintype.sum_bool, cf]; simp [sz]
  have e2 : modExp (fun i => Fin (sz u v i true)) false = (v : ℤ) := by
    unfold modExp; simp only [Finset.sum_filter, Fintype.sum_bool, cf]; simp [sz]
  have e3 : modExp (Two (Fin u) (Fin v)) true = -(u : ℤ) := by
    unfold modExp; simp only [Finset.sum_filter, Fintype.sum_bool]; simp [cf]
  have e4 : modExp (Two (Fin u) (Fin v)) false = (v : ℤ) := by
    unfold modExp; simp only [Finset.sum_filter, Fintype.sum_bool]; simp [cf]
  refine TensorProduct.ext' fun x y => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, colRep, extTensor_tmul, detRep,
    ofChar_apply, deltaHalf_apply, Fintype.prod_bool]
  rw [e1, e2, e3, e4]
  simp only [detChar_apply, MonoidHom.prod_apply, Pi.evalMonoidHom_apply, colChar, cond_true]
  rw [hA, hD]
  rfl

end GlobalTheory.SmGL.RowOneCell
