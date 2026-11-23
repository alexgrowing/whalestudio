import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem charpoly_eq_of_eqOn_dense : ∀ {X A : Type} [TopologicalSpace X] [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Infinite A] {n : ℕ} (M N : X → Matrix (Fin n) (Fin n) A), Continuous M → Continuous N → ∀ U : Set X, Dense U → (∀ x ∈ U, (M x).charpoly = (N x).charpoly) → ∀ x, (M x).charpoly = (N x).charpoly := by
  intro X A _ _ _ _ _ _ n M N hM hN U hU hEq x
  apply Polynomial.funext
  intro c
  have hcM : Continuous fun y => (M y).charpoly.eval c := by
    simp_rw [Matrix.eval_charpoly]
    exact (continuous_const.sub hM).matrix_det
  have hcN : Continuous fun y => (N y).charpoly.eval c := by
    simp_rw [Matrix.eval_charpoly]
    exact (continuous_const.sub hN).matrix_det
  have h : (fun y => (M y).charpoly.eval c) = fun y => (N y).charpoly.eval c :=
    Continuous.ext_on hU hcM hcN (fun y hy => by simp only [hEq y hy])
  exact congrFun h x

end GlobalTheory
