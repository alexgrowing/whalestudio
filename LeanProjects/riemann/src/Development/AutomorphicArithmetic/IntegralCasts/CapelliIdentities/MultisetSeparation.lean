import Mathlib

open Polynomial in
private lemma eval_prod_add (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod).eval u
      = (m.map (fun x : ℂ ↦ u + x)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul, ih, eval_sub, eval_X, eval_C]
    ring

theorem UpperTheory.Reformulated.B.MultisetSeparation.msetSep :
    ∀ (m m' : Multiset ℂ),
    (∀ (u : ℂ), (Multiset.map (fun (x : ℂ) ↦ u + x) m).prod = (Multiset.map (fun (x : ℂ) ↦ u + x) m').prod) → m = m' := by
  intro m m' h
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod
      = ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_add, eval_prod_add, h u]
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr
