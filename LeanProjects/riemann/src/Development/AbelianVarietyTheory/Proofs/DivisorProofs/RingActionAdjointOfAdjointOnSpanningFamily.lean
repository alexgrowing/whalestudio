import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AdjSpan

open GlobalTheory.CechPic

theorem adj_of_span : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ∀ (act : O → (A ⟶ A)), IsRAct A act → (∀ i, LBIso (Q.pull (lift (fst A A ≫ act (e i)) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar (e i)))).left)) → Adj A Q bar act := by
  intro S A _ _ Q hQ O _ bar r e hbar hspan act hact he
  obtain ⟨hA, hL, h₁, h₂, -, hamp⟩ := hQ
  have hbi := GlobalTheory.Biadditive.biadditive_of_triv_axes GlobalTheory.globalFns_holds S A _ hA (pull_isLB hL _) hamp Q hL h₁ h₂

  let B : ((A ⊗ A) ⟶ A) → ((A ⊗ A) ⟶ A) → Pic (A ⊗ A).left := fun u v => pull (lift u v).left (cls Q hL)
  have addL : ∀ u u' v, B (u * u') v = B u v + B u' v := fun u u' v => by
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 (hbi (A ⊗ A) u u' v).1
    rw [cls_linComb hL, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    show pull _ _ = pull _ _ + pull _ _
    rw [← sub_eq_zero, ← z]
    abel
  have addR : ∀ u v v', B u (v * v') = B u v + B u v' := fun u v v' => by
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 (hbi (A ⊗ A) v v' u).2
    rw [cls_linComb hL, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    show pull _ _ = pull _ _ + pull _ _
    rw [← sub_eq_zero, ← z]
    abel
  let f : O → Pic (A ⊗ A).left := fun a => B (fst A A ≫ act a) (snd A A) - B (fst A A) (snd A A ≫ act (bar a))
  have fadd : ∀ a b, f (a + b) = f a + f b := fun a b => by
    simp only [f]
    rw [hbar, hact.2.2.2, hact.2.2.2, MonObj.comp_mul, MonObj.comp_mul, addL, addR]
    abel
  let F : O →+ Pic (A ⊗ A).left := AddMonoidHom.mk' f fadd
  have Fe : ∀ i, F (e i) = 0 := fun i => by
    show f (e i) = 0
    exact sub_eq_zero.2 ((cls_eq_iff (pull_isLB hL _) (pull_isLB hL _)).2 (he i))
  have hker : Submodule.span ℤ (Set.range e) ≤ LinearMap.ker F.toIntLinearMap :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Fe i)
  intro a
  have ha : F a = 0 := hker (hspan ▸ Submodule.mem_top : a ∈ Submodule.span ℤ (Set.range e))
  exact (cls_eq_iff (pull_isLB hL _) (pull_isLB hL _)).1 (sub_eq_zero.1 ha)

end GlobalTheory.AdjSpan
