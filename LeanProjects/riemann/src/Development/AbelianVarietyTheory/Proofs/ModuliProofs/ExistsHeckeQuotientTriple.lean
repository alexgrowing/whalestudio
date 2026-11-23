import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G G' T T' : Over S} [GrpObj G] [GrpObj G']

def lam (c : Pic G.left) (x y : T ⟶ G) : Pic T.left :=
  pull (x * y).left c - pull x.left c - pull y.left c + pull (1 : T ⟶ G).left c

theorem cls_cube_two {L : LB G.left} (hL : L.IsLB) (x y : T ⟶ G) (h : (cubeLB G ![x, y] L).IsLB) :
    cls _ h = lam (cls L hL) x y := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.sum_comp Equiv.ulift.symm,
    show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e : ((-1 : ℤ) ^ 2) • pull (1 : T ⟶ G).left (cls L hL) + (((-1 : ℤ) ^ 1) • pull (x * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (y * 1).left (cls L hL) + ((-1 : ℤ) ^ 0) • pull (x * (y * 1)).left (cls L hL))) =
      lam (cls L hL) x y := by
    simp only [_root_.mul_one, lam]
    norm_num
    abel
  exact e

theorem cls_cube_three [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (x y z : T ⟶ G)
    (h : (cubeLB G ![x, y, z] L).IsLB) :
    cls _ h = lam (cls L hL) (x * y) z - lam (cls L hL) x z - lam (cls L hL) y z := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.sum_comp Equiv.ulift.symm,
    show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have e : ((-1 : ℤ) ^ 3) • pull (1 : T ⟶ G).left (cls L hL) + (((-1 : ℤ) ^ 2) • pull (x * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 2) • pull (y * 1).left (cls L hL) + (((-1 : ℤ) ^ 2) • pull (z * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (x * (y * 1)).left (cls L hL) + (((-1 : ℤ) ^ 1) • pull (x * (z * 1)).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (y * (z * 1)).left (cls L hL) +
        ((-1 : ℤ) ^ 0) • pull (x * (y * (z * 1))).left (cls L hL))))))) =
      lam (cls L hL) (x * y) z - lam (cls L hL) x z - lam (cls L hL) y z := by
    simp only [_root_.mul_one, lam, _root_.mul_assoc]
    norm_num
    abel
  exact e

theorem pull_lam (h : T' ⟶ T) (c : Pic G.left) (x y : T ⟶ G) :
    pull h.left (lam c x y) = lam c (h ≫ x) (h ≫ y) := by
  simp only [lam, map_add, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_one]

theorem lam_pull (ψ : G ⟶ G') [IsMonHom ψ] (c : Pic G'.left) (x y : T ⟶ G) :
    lam (pull ψ.left c) x y = lam c (x ≫ ψ) (y ≫ ψ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, MonObj.mul_comp, MonObj.one_comp]

theorem lam_nsmul (n : ℕ) (c : Pic G.left) (x y : T ⟶ G) : lam (n • c) x y = n • lam c x y := by
  simp only [lam, map_nsmul, nsmul_add, nsmul_sub]

theorem lam_one_left (c : Pic G.left) (y : T ⟶ G) : lam c 1 y = 0 := by
  simp only [lam, _root_.one_mul]; abel

theorem lam_one_right (c : Pic G.left) (x : T ⟶ G) : lam c x 1 = 0 := by
  simp only [lam, _root_.mul_one]; abel

variable [IsCommMonObj G]

theorem lam_comm (c : Pic G.left) (x y : T ⟶ G) : lam c x y = lam c y x := by
  simp only [lam, _root_.mul_comm x y]; abel

theorem lam_mul_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y z : T ⟶ G) :
    lam (cls L hL) (x * y) z = lam (cls L hL) x z + lam (cls L hL) y z := by
  have h₀ := (cls_eq_zero_iff (N := Theta G L) (LB.isLB_linComb hL _ _)).2 hΘ
  have h₁ := (cls_cube_three hL (fst _ _) (snd _ _ ≫ fst _ _) (snd G (G ⊗ G) ≫ snd _ _)
    (LB.isLB_linComb hL _ _)).symm.trans h₀
  have h₂ := congrArg (pull (lift x (lift y z)).left) h₁
  simp only [map_sub, map_zero, pull_lam, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_snd] at h₂
  rw [sub_sub, sub_eq_zero] at h₂
  exact h₂

theorem lam_pow_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℕ) :
    lam (cls L hL) (x ^ n) z = n • lam (cls L hL) x z := by
  induction n with
  | zero => rw [pow_zero, lam_one_left, zero_nsmul]
  | succ n ih => rw [pow_succ, lam_mul_left hL hΘ, ih, succ_nsmul]

theorem lam_pow_right {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℕ) :
    lam (cls L hL) x (z ^ n) = n • lam (cls L hL) x z := by
  rw [lam_comm, lam_pow_left hL hΘ, lam_comm]

theorem sym_of_isSymmetric (L : RigLB G) (h : L.IsSymmetric) : Out.Sym G L.L := by
  obtain ⟨_, w, hw, -⟩ := h
  have e := (cls_eq_iff L.isLB (pull_isLB L.isLB _)).2 ⟨w, hw⟩
  rw [cls_pull L.isLB] at e
  refine fun s => ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).1 ?_⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, ← e, one_smul, neg_smul, add_neg_cancel]

end Pairing

theorem dense_image_points {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} [LocallyOfFiniteType A.hom]
    (f : A ⟶ B) [Surjective f.left] (P : Set (𝟙_ (Over (Sp k)) ⟶ B)) (hP : ∀ u : 𝟙_ (Over (Sp k)) ⟶ A, u ≫ f ∈ P) :
    Dense (⋃ x ∈ P, Set.range x.left) := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hd : Dense (closedPoints A.left) := dense_iff_closure_eq.2 closure_closedPoints
  refine (f.left.surjective.denseRange.dense_image f.left.continuous hd).mono ?_
  rintro _ ⟨a, ha, rfl⟩
  let u : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk (pointOfClosedPoint A.hom a ha) (pointOfClosedPoint_comp A.hom a ha)
  refine Set.mem_iUnion₂.2 ⟨u ≫ f, hP u, ⟨(default : PrimeSpectrum k), ?_⟩⟩
  exact congrArg f.left (pointOfClosedPoint_apply A.hom a ha _)

end GlobalTheory.CechPic

namespace GlobalTheory

open CechPic

end GlobalTheory
