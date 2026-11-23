import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem siegPre_bundle_mul_left : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → ∀ (T : Over (Sp K)) (x x' y : T ⟶ c.A), ∃ t : LB.Gen (LB.LinComb c.P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen := by
  intro hΘ K _ o _ s h k ζ c P pr hpr huniv T x x' y
  have := hpr 0
  have := hpr 1

  have hL : (c.P.pull (lift (pr 0) (pr 1)).left).IsLB := pull_isLB c.isLB _
  have hθ := hΘ (Sp K) P _ hL

  have hpt : ∀ z : T ⟶ P.A, CechPic.pull z.left (cls _ hL) =
      CechPic.pull (lift (z ≫ pr 0) (z ≫ pr 1)).left (cls c.P c.isLB) := by
    intro z
    rw [cls_pull c.isLB _ hL, ← pull_comp, ← Over.comp_left, comp_lift]

  have hax₁ : ∀ v : T ⟶ c.A, CechPic.pull (lift (1 : T ⟶ c.A) v).left (cls c.P c.isLB) = 0 := by
    intro v
    have e : lift (1 : T ⟶ c.A) v = v ≫ lift (1 : c.A ⟶ c.A) (𝟙 c.A) := by
      rw [comp_lift, comp_one, Category.comp_id]
    rw [e, Over.comp_left, pull_comp, ← cls_pull c.isLB _ (pull_isLB c.isLB _),
      (cls_eq_zero_iff _).2 c.rig₁, map_zero]
  have hax₂ : ∀ u : T ⟶ c.A, CechPic.pull (lift u (1 : T ⟶ c.A)).left (cls c.P c.isLB) = 0 := by
    intro u
    have e : lift u (1 : T ⟶ c.A) = u ≫ lift (𝟙 c.A) (1 : c.A ⟶ c.A) := by
      rw [comp_lift, comp_one, Category.comp_id]
    rw [e, Over.comp_left, pull_comp, ← cls_pull c.isLB _ (pull_isLB c.isLB _),
      (cls_eq_zero_iff _).2 c.rig₂, map_zero]

  obtain ⟨a, ha, -⟩ := huniv T (fun u => if u = 0 then x else 1)
  obtain ⟨b, hb, -⟩ := huniv T (fun u => if u = 0 then x' else 1)
  obtain ⟨d, hd, -⟩ := huniv T (fun u => if u = 1 then y else 1)
  have ha0 : a ≫ pr 0 = x := by simpa using ha 0
  have ha1 : a ≫ pr 1 = 1 := by simpa using ha 1
  have hb0 : b ≫ pr 0 = x' := by simpa using hb 0
  have hb1 : b ≫ pr 1 = 1 := by simpa using hb 1
  have hd0 : d ≫ pr 0 = 1 := by simpa using hd 0
  have hd1 : d ≫ pr 1 = y := by simpa using hd 1

  have key := lam_mul_left hL hθ a b d
  have e1 : x * x' * (1 : T ⟶ c.A) = x * x' := by rw [_root_.mul_one]
  have e3 : (1 : T ⟶ c.A) * 1 = 1 := by rw [_root_.one_mul]
  have e4 : x * (1 : T ⟶ c.A) = x := by rw [_root_.mul_one]
  have e5 : x' * (1 : T ⟶ c.A) = x' := by rw [_root_.mul_one]
  have e6 : (1 : T ⟶ c.A) * y = y := by rw [_root_.one_mul]
  simp only [lam, hpt, mul_comp, ha0, ha1, hb0, hb1, hd0, hd1, one_comp, e1, e3, e4, e5, e6] at key
  simp only [hax₁, hax₂, sub_zero, add_zero] at key
  refine (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).1 ?_
  rw [cls_linComb c.isLB, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, one_smul, neg_smul]
  rw [key]
  abel

end GlobalTheory
