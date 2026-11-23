import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TrivSubgroup

variable {D : D7} {q : ℕ}

theorem zeroAt_zero : ZeroAt D q 0 := fun k =>
  ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

theorem zeroAt_add {x y : AE D} (hx : ZeroAt D q x) (hy : ZeroAt D q y) : ZeroAt D q (x + y) := by
  intro k
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx k
  obtain ⟨m', hm', hmq', s', hs', h'⟩ := hy k
  refine ⟨m * m', Nat.mul_pos hm hm', Nat.Coprime.mul_left hmq hmq', (m' : AE D) * s + (m : AE D) * s',
    add_mem (mul_mem (natCast_mem _ _) hs) (mul_mem (natCast_mem _ _) hs'), ?_⟩
  push_cast
  linear_combination (m' : AE D) * h + (m : AE D) * h'

theorem zeroAt_mul_left (hq : q.Prime) (y : AE D) {x : AE D} (hx : ZeroAt D q x) :
    ZeroAt D q (y * x) := by
  intro k
  obtain ⟨n, hn, hy⟩ := GlobalTheory.AdelicApprox.exists_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx (k + a)
  refine ⟨m * n', Nat.mul_pos hm (Nat.pos_of_ne_zero (by rintro rfl; simp at hn')),
    Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, _, mul_mem hs hy, ?_⟩
  push_cast
  linear_combination (n' : AE D) * y * h

def zeroIdeal (D : D7) (hq : q.Prime) : Ideal (AE D) where
  carrier := {x | ZeroAt D q x}
  add_mem' := zeroAt_add
  zero_mem' := zeroAt_zero
  smul_mem' := fun c _ hx => zeroAt_mul_left hq c hx

theorem entry_mul_mem {R : Type} [CommRing R] (I : Ideal R) {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hB : ∀ i j, B i j ∈ I) (i j : Fin n) : (A * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hB k j)

theorem trivAt_subgroup : ∀ (D : D7) (n q : ℕ), q.Prime → TrivAt D q (1 : GL (Fin n) (AE D)) ∧
    (∀ g h : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q h → TrivAt D q (g * h)) ∧
    ∀ g : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q g⁻¹ := by
  intro D n q hq
  refine ⟨fun i j => ?_, fun g h hg hh i j => ?_, fun g hg i j => ?_⟩
  · rw [Units.val_one, sub_self]; exact zeroAt_zero
  · have e : ((g * h : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) - 1 =
        (g : Matrix (Fin n) (Fin n) (AE D)) * ((h : Matrix (Fin n) (Fin n) (AE D)) - 1) +
          ((g : Matrix (Fin n) (Fin n) (AE D)) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel]
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact zeroAt_add (entry_mul_mem (zeroIdeal D hq) _ _ hh i j) (hg i j)
  · have e : ((g⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) - 1 =
        (-((g⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D))) *
          ((g : Matrix (Fin n) (Fin n) (AE D)) - 1) := by
      rw [neg_mul, mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [← Matrix.sub_apply, e]
    exact entry_mul_mem (zeroIdeal D hq) _ _ hg i j

end GlobalTheory.TrivSubgroup
