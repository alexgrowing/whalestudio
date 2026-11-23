import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.UnipPlaced

variable {R : Type} [CommRing R]

theorem mul_apply_succ {n : ℕ} {X Y : GL (Fin n) R} (hX : X ∈ unipB R (Fin n)) (hY : Y ∈ unipB R (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X * Y : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a a' =
      (X : Matrix (Fin n) (Fin n) R) a a' + (Y : Matrix (Fin n) (Fin n) R) a a' := by
  rw [mem_unipB] at hX hY
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [hX.2 a, hY.2 a', one_mul, mul_one, add_comm]
  · intro c _ hc
    have h1 := Fin.val_injective.ne hc.1
    have h2 := Fin.val_injective.ne hc.2
    by_cases hca : c < a
    · rw [hX.1 a c hca, zero_mul]
    · have : a' < c := by rw [Fin.lt_iff_val_lt_val] at hca ⊢; omega
      rw [hY.1 c a' this, mul_zero]

end GlobalTheory.GamMul.UnipPlaced

namespace GlobalTheory.GamMul.UnipPlaced

variable {R : Type} [CommRing R]

theorem superDiag_mul_unip {n : ℕ} {u v : GL (Fin n) R} (hu : u ∈ unipB R (Fin n)) (hv : v ∈ unipB R (Fin n)) :
    superDiag (u * v) = superDiag u + superDiag v := by
  simp only [superDiag, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
    mul_apply_succ hu hv (Finset.mem_filter.1 hj).2

end GlobalTheory.GamMul.UnipPlaced
