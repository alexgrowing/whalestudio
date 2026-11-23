import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEqStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.fv_add_h_res {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}
    {t : G.TorsionTower A} {c : primDR A} (d : Dat t c) (n : ℕ) (D : Type) [CommRing D] [Algebra R D]
    (φ : G.A n →ₐ[R] D) :
    fv d.f (G.A (n + 1)) D (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (t.y (n + 1)) +
      (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (d.h (n + 1)) = fv d.f (G.A n) D φ (t.y n) + φ (d.h n) := by
  have hc := (_root_.GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R A d.f).1 (G.A (n + 1)) (G.A n) D
    (G.res n : G.A (n + 1) →ₐ[R] G.A n) φ (t.y (n + 1)) (sm_whole _)
  rw [hc, t.res n, d.res n, AlgHom.comp_apply, map_sub]
  simp only [BialgHom.coe_toAlgHom]
  abel

theorem Dat.pullTwo_res_coc (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n := by

  let L : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeLeft
  let Rt : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeRight
  have hres : ∀ u : G.A (n + 1) ⊗[R] G.A (n + 1), pullbackTwo (G.res n) u =
      Algebra.TensorProduct.lift (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))
        (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (fun _ _ ↦ Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [L, Rt]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hid : ∀ u : G.A n ⊗[R] G.A n,
      Algebra.TensorProduct.lift L Rt (fun _ _ ↦ Commute.all _ _) u = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [L, Rt]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmul : (toConv (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) *
      toConv (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))).ofConv =
      (toConv L * toConv Rt).ofConv.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n) :=
    (AlgHom.convMul_comp_bialgHom_distrib (toConv L) (toConv Rt) (G.res n)).symm
  rw [hres, _root_.GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue, hmul, d.fv_add_h_res n, d.fv_add_h_res n, d.fv_add_h_res n]
  conv_rhs => rw [← hid (d.coc n), _root_.GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue]
  simp only [← spOver_comp, Category.assoc, t.res]

end GlobalTheory.PtExt
