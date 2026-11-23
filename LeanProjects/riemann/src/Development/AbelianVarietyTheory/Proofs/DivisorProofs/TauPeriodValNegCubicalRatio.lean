import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TauNeg

theorem val_tau_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (D.tau (-a) (-b)) (𝟙 _) z J * cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c (-a)) (toUnit (TK R) ≫ D.c b) * (cubV D.cub z J (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c (-b)) (toUnit (TK R) ≫ D.c (-a)))⁻¹ := by
  intro R _ _ D hB a b z J hJ
  have xadd : ∀ u v : D.X, toUnit (TK R) ≫ D.c (u + v) = (toUnit (TK R) ≫ D.c u) * (toUnit (TK R) ≫ D.c v) := by
    intro u v; rw [D.c_add]; exact MonObj.comp_mul _ _ _
  have x0 : toUnit (TK R) ≫ D.c 0 = 1 := by
    have h := xadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have C := isCub_cubV D.cub hJ
  have B : ∀ u u' w v : D.X, u + u' = w → val (D.tau w v) (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) =
      val (D.tau u v) (𝟙 _) z J * val (D.tau u' v) (𝟙 _) z J := by
    rintro u u' w v rfl
    have h := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))
    have hc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 u u' v)) (𝟙 _) z J =
        cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) := by
      refine (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans ?_
      rw [Category.id_comp, Category.id_comp, Category.id_comp]
    rw [← hc]
    exact h
  have sym : ∀ u v : D.X, val (D.tau u v) (𝟙 _) z J = val (D.tau v u) (𝟙 _) z J := by
    intro u v
    simp only [DegPre.tau, val_mul hJ, val_inv]
    rw [add_comm u v, mul_right_comm (val (D.psi (v + u)) (𝟙 _) z J)]
  have T0 : ∀ v : D.X, val (D.tau 0 v) (𝟙 _) z J = 1 := by
    intro v
    have h := B 0 v v v (zero_add v)
    rw [x0, C.face, _root_.mul_one] at h
    exact (mul_eq_right.1 h.symm)
  have e1 := B a (-a) 0 b (add_neg_cancel a)
  have e2 := B b (-b) 0 (-a) (add_neg_cancel b)
  rw [T0, _root_.one_mul] at e1 e2
  rw [e1, e2, sym b (-a), sym (-b) (-a)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TauNeg
