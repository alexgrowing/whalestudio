import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal.Conn

theorem pow_apply_smul_nsmul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      k.choose p • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_choose_succ_nsmul (fun i j => (fun τ => (⇑(derivative K))^[i] (f τ)) • (C.nabla ^ j) v) k,
      pow_succ', Module.End.mul_apply, ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
    rw [map_nsmul, C.leibniz, smul_add, add_comm]
    congr 2
    · rw [show k + 1 - p = k - p + 1 by omega, pow_succ', Module.End.mul_apply]
    · congr 1
      funext τ
      rw [Function.iterate_succ_apply']

theorem pow_apply_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  rw [pow_apply_smul_nsmul]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm

end GlobalTheory.BKReal.Conn
