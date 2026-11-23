import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColProd

theorem tsum_pow_fin {α : Type*} (f : α → ℝ≥0∞) (n : ℕ) :
    ∑' g : Fin n → α, ∏ j, f (g j) = (∑' v, f v) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n + 1) => α))]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod (f := fun a (g : Fin n → α) => f a * ∏ i, f (g i))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih, pow_succ']

theorem absTheta_le_pow_of_colProd : ∀ (D : D7) (V : HSp D) {n : ℕ} (φ : Mx D V.rank n → ℂ) (ρ : Mx D V.rank 1 → ℝ≥0∞) (C : ℝ≥0∞) (y : GA D V), (∀ x : Mx D V.rank n, ‖φ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ ≤ C * ∏ j : Fin n, ρ (fun i (_ : Fin 1) => x i j)) → ∀ a : GA D V, absTheta V φ (a * y) ≤ C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ρ (invPt V a ξ)) ^ n := by
  intro D V n φ ρ C y hφ a
  have hstep : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      ‖φ (invPt V (a * y) ξ)‖ₑ ≤ C * ∏ j : Fin n, ρ (invPt V a (fun i (_ : Fin 1) => ξ i j)) := by
    intro ξ
    have h1 : invPt V (a * y) ξ =
        (HMul.hMul (mt V y⁻¹) (invPt V a ξ) : Matrix (Fin V.rank) (Fin n) (AE D)) := by
      simp only [invPt, mul_inv_rev, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.mul_assoc]
    rw [h1]
    refine (hφ (invPt V a ξ)).trans (le_of_eq ?_)
    congr 1
  let e : (Fin n → Matrix (Fin V.rank) (Fin 1) D.host.E) ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun g i j => g j i 0
      invFun := fun ξ j i _ => ξ i j
      left_inv := fun g => by
        funext j i u
        show g j i 0 = g j i u
        rw [Fin.fin_one_eq_zero u]
      right_inv := fun ξ => by rfl }
  calc absTheta V φ (a * y)
      = ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖φ (invPt V (a * y) ξ)‖ₑ := by rfl
    _ ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          C * ∏ j : Fin n, ρ (invPt V a (fun i (_ : Fin 1) => ξ i j)) := ENNReal.tsum_le_tsum hstep
    _ = C * ∑' g : Fin n → Matrix (Fin V.rank) (Fin 1) D.host.E, ∏ j : Fin n, ρ (invPt V a (g j)) := by
        rw [ENNReal.tsum_mul_left, ← Equiv.tsum_eq e]
        congr 1
        refine tsum_congr (fun g => Finset.prod_congr rfl (fun j _ => ?_))
        congr 2
        funext i u
        show g j i 0 = g j i u
        rw [Fin.fin_one_eq_zero u]
    _ = C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ρ (invPt V a ξ)) ^ n := by
        rw [tsum_pow_fin (fun v => ρ (invPt V a v)) n]

end GlobalTheory.CompanionTheory.ColProd
