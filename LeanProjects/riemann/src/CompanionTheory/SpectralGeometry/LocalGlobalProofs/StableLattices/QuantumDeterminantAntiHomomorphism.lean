import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgTransport

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

theorem anti_list_prod {A B : Type} [Ring A] [Ring B] (f : A → B) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f y * f x) (l : List A) :
    f l.prod = (l.map f).reverse.prod := by
  induction l with
  | nil => simpa using h1
  | cons a l ih => simp [List.prod_cons, hm, ih]

theorem anti_Tm {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B) (h1 : f 1 = 1)
    {m : ℕ} (E : Fin m → Fin m → A) (v : ℂ) (a b : Fin m) :
    f (Tm E v a b) = Tm (fun a b => f (E b a)) v b a := by
  have hal : f (algebraMap ℂ A v) = algebraMap ℂ B v := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, h1]
  unfold Tm
  by_cases h : a = b
  · subst h; simp [hal]
  · simp [h, Ne.symm h]

theorem qdet_eq_qminorRow_rev {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E)
    (u : ℂ) : qdet E u = PI.qminorRow E (id ∘ Fin.revPerm) (id ∘ Fin.revPerm) u := by
  have hrow : PI.RowForm := quantum_minor_row_form
  rw [← hrow A m m E hE, quantumMinorRowSkew_holds A m m E id _ Fin.revPerm u,
    quantumMinorColSkew_holds A m m E hE id id Fin.revPerm u, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rfl

theorem qdet_anti {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f y * f x) {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E) (u : ℂ) :
    qdet (fun a b => f (E b a)) u = f (qdet E u) := by
  rw [qdet_eq_qminorRow_rev E hE]
  unfold qdet qminor PI.qminorRow
  rw [map_sum]
  refine (Fintype.sum_equiv (PI.UnitaryGroupMassFormula.QmRowForm.revConj m) _ _ (fun σ => ?_)).symm
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, PI.UnitaryGroupMassFormula.QmRowForm.sign_revConj,
    anti_list_prod f h1 hm, List.map_ofFn, PI.UnitaryGroupMassFormula.QmRowForm.reverse_ofFn']
  congr 2
  refine List.ofFn_inj.mpr (funext fun k => ?_)
  simp only [Function.comp_apply, anti_Tm f h1, id]
  show Tm _ _ _ _ = Tm _ _ (Fin.revPerm (σ (Fin.revPerm k))) _
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  congr 1
  rw [Nat.cast_sub (by omega : (k : ℕ) + 1 ≤ m)]
  push_cast
  ring

end GlobalTheory.CompanionTheory.RgTransport
