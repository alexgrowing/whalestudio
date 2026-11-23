import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private def Up (g : GL (Fin 3) R) : Prop := Matrix.BlockTriangular (g : Matrix (Fin 3) (Fin 3) R) id

private theorem ltd_wt_neg_iff (a b : Fin 3) : wt a b < 0 ↔ b < a := by
  revert a b; decide

private theorem Up.mul {g h : GL (Fin 3) R} (hg : Up g) (hh : Up h) : Up (g * h) :=
  Matrix.BlockTriangular.mul hg hh

private theorem Up.inv {g : GL (Fin 3) R} (hg : Up g) : Up g⁻¹ := by
  letI : Invertible (g : Matrix (Fin 3) (Fin 3) R) := g.invertible
  have := Matrix.blockTriangular_inv_of_blockTriangular hg
  unfold Up
  rwa [Matrix.coe_units_inv]

private theorem Jc (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) a b = X b.rev a.rev := by
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

private theorem ltd_theta_apply (g : GL (Fin 3) R) (a b : Fin 3) :
    (theta g : Matrix (Fin 3) (Fin 3) R) a b = ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) b.rev a.rev := by
  rw [theta_val, Jc]

private theorem Up.theta {g : GL (Fin 3) R} (hg : Up g) : Up (theta g) := by
  intro a b h
  rw [ltd_theta_apply]
  exact hg.inv (Fin.rev_lt_rev.mpr h)

private theorem Up.sgn {g : GL (Fin 3) R} (hg : Up g) (s : ℤˣ) : Up (sgnAct 3 R s g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rwa [sgnAct_one]
  · rw [sgnAct_neg_one]; exact hg.theta

private theorem Up.diag_mul {g h : GL (Fin 3) R} (hg : Up g) (hh : Up h) (a : Fin 3) :
    ((g * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a =
      (g : Matrix (Fin 3) (Fin 3) R) a a * (h : Matrix (Fin 3) (Fin 3) R) a a := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h1 | h1
    · rw [hg (show id b < id a from h1), zero_mul]
    · rw [hh (show id a < id b from h1), mul_zero]
  · simp

private def dgl (g : GL (Fin 3) R) (hg : Up g) : GL (Fin 3) R where
  val := Matrix.diagonal fun a => (g : Matrix (Fin 3) (Fin 3) R) a a
  inv := Matrix.diagonal fun a => ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← hg.diag_mul hg.inv, mul_inv_cancel]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← hg.inv.diag_mul hg, inv_mul_cancel]
    simp

private theorem dgl_val (g : GL (Fin 3) R) (hg : Up g) : (dgl g hg : Matrix (Fin 3) (Fin 3) R) =
    Matrix.diagonal fun a => (g : Matrix (Fin 3) (Fin 3) R) a a := rfl

private theorem dgl_inv_val (g : GL (Fin 3) R) (hg : Up g) :
    (((dgl g hg)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
    Matrix.diagonal fun a => ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a := rfl

private theorem dgl_mul {g h : GL (Fin 3) R} (hg : Up g) (hh : Up h) :
    dgl (g * h) (hg.mul hh) = dgl g hg * dgl h hh := by
  apply Units.ext
  rw [Units.val_mul (dgl g hg), dgl_val, dgl_val, dgl_val, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact hg.diag_mul hh a

private theorem dgl_sgn {g : GL (Fin 3) R} (hg : Up g) (s : ℤˣ) :
    dgl (sgnAct 3 R s g) (hg.sgn s) = sgnAct 3 R s (dgl g hg) := by
  apply Units.ext
  rw [dgl_val]
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one, sgnAct_one, dgl_val]
  · rw [sgnAct_neg_one, sgnAct_neg_one]
    ext a b
    rw [ltd_theta_apply, dgl_inv_val]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ltd_theta_apply]
    · rw [Matrix.diagonal_apply_ne _ hab,
        Matrix.diagonal_apply_ne _ (fun h => hab (Fin.rev_injective h).symm)]

private def Bor (R : Type) [CommRing R] : Subgroup (GG 3 R) where
  carrier := {x | Up x.left}
  mul_mem' := fun {x y} hx hy => by
    change Up (x * y).left
    rw [SemidirectProduct.mul_left]
    exact Up.mul hx (Up.sgn hy _)
  one_mem' := Matrix.blockTriangular_one
  inv_mem' := fun {x} hx => by
    change Up (x⁻¹).left
    rw [SemidirectProduct.inv_left]
    exact Up.sgn (Up.inv hx) _

private def dgHom (R : Type) [CommRing R] : Bor R →* GG 3 R :=
  MonoidHom.mk' (fun x => ⟨dgl x.1.left x.2, x.1.right⟩) (fun x y => by
    ext1
    · rw [SemidirectProduct.mul_left]
      change dgl (x.1.left * sgnAct 3 R x.1.right y.1.left) (Up.mul x.2 (Up.sgn y.2 _)) =
        dgl x.1.left x.2 * sgnAct 3 R x.1.right (dgl y.1.left y.2)
      exact (dgl_mul (g := x.1.left) x.2 (Up.sgn (g := y.1.left) y.2 _)).trans
        (congrArg (dgl x.1.left x.2 * ·) (dgl_sgn (g := y.1.left) y.2 _))
    · rfl)

end SlopeTestRemainingChoices

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.lt_diag :
    ∀ {R : Type} [CommRing R] [Finite R], ∃ (B : Subgroup (GG 3 R)) (dg : B →* GG 3 R),
      (∀ x : GG 3 R, x ∈ B ↔ ∀ a b, wt a b < 0 → x.mat a b = 0) ∧
      ∀ x : B, (dg x).right = (x : GG 3 R).right ∧ (dg x).mat = Matrix.diagonal fun a => (x : GG 3 R).mat a a := by
  intro R _ _
  refine ⟨Bor R, dgHom R, fun x => ?_, fun x => ⟨rfl, rfl⟩⟩
  exact ⟨fun h a b hab => h ((ltd_wt_neg_iff a b).1 hab), fun h a b hab => h a b ((ltd_wt_neg_iff a b).2 hab)⟩
