import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.DescFalling

theorem desc_eq_X_pow_smul_nabla_pow {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι) :
    C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  have hX : ∀ w, C.nabla ((X : K⟦X⟧) • w) = w + (X : K⟦X⟧) • C.nabla w := fun w => by
    have h := C.leibniz (fun _ => X) w
    have e1 : ∀ u : Vec K a ι, ((fun _ => (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • u = (X : K⟦X⟧) • u :=
      fun u => rfl
    have e2 : ((fun _ => PowerSeries.derivative K (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • w = w := by
      simp only [PowerSeries.derivative_X]
      exact one_smul _ w
    rw [e1, e1, e2] at h
    exact h
  have hcomm : ∀ (j : ℕ) (w : Vec K a ι),
      (C.nabla ^ j) ((X : K⟦X⟧) • C.nabla w) = (X : K⟦X⟧) • (C.nabla ^ (j + 1)) w + j • (C.nabla ^ j) w := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih, map_add, hX, map_nsmul, pow_succ' C.nabla (j + 1),
        Module.End.mul_apply, pow_succ' C.nabla j, Module.End.mul_apply, succ_nsmul]
      abel
  induction k generalizing v with
  | zero => simp [Conn.desc_zero]
  | succ k ih =>
    rw [Conn.desc_succ, ih, Conn.N_apply, map_sub, hcomm, map_nsmul, add_sub_cancel_right, smul_smul,
      ← pow_succ]

end GlobalTheory.DescFalling
