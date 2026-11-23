import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRepSubgroupEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

namespace GlobalTheory.ParabConj

theorem stdBlocks_lt {s r : ℕ} (d : Fin s → ℕ) (hd : ∑ i, d i = r) {a b : Fin s} (i : Fin (d a)) (j : Fin (d b))
    (hba : b < a) : stdBlocks d hd ⟨b, j⟩ < stdBlocks d hd ⟨a, i⟩ := by
  let f : ℕ → ℕ := fun n => if h : n < s then d ⟨n, h⟩ else 0
  have key : ∀ c : Fin s, ∑ x : Fin c, d (Fin.castLE c.2.le x) = ∑ x ∈ Finset.range c, f x := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < s := x.2.trans c.2
    simp only [f, hx, dif_pos]
    rfl
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, key, key]
  have h1 : ∑ x ∈ Finset.range (b + 1), f x ≤ ∑ x ∈ Finset.range a, f x :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hba))
  rw [Finset.sum_range_succ] at h1
  have h2 : f b = d b := by simp [f]
  have := j.2
  omega

theorem mem_stdMaxParab_of_le_conjBy (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r) (g : GL (Fin r) F) (H : parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h)) :
    g ∈ stdMaxParab F h := by
  by_contra hg
  have hg' := hg
  rw [mem_stdMaxParab] at hg'
  push Not at hg'
  obtain ⟨q, j, hj, hq, hne⟩ := hg'
  refine hg (inv_mem_iff.1 ((mem_stdMaxParab h).2 fun i p hp hi => ?_))
  have hpq : p < q := by rw [Fin.lt_def]; omega
  let t : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection p q (1 : F))
    (by rw [Matrix.det_transvection_of_ne p q hpq.ne]; exact one_ne_zero)
  have ht : (t : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single p q 1 := rfl
  have htP : t ∈ parab F (stdBlocks d hd) := by
    refine mem_parab_iff.2 fun x y u v hyx => ?_
    have hlt := stdBlocks_lt d hd u v hyx
    rw [ht, Matrix.add_apply, Matrix.one_apply_ne hlt.ne', zero_add]
    refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨e1, e2⟩
    rw [← e1, ← e2] at hlt
    exact lt_asymm hlt hpq
  have h0 := (mem_stdMaxParab h).1 (mem_conjBy.1 (H htP)) i j hj hi
  have hij : i ≠ j := by rintro rfl; omega
  have hmul : ((g⁻¹ * t * g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * Matrix.single p q (1 : F) *
        (g : Matrix (Fin r) (Fin r) F) := by
    rw [Units.val_mul, Units.val_mul, ht, mul_add, add_mul, mul_one, Units.inv_mul]
  rw [hmul, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, Matrix.mul_apply,
    Finset.sum_eq_single q (fun x _ hx => by rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hx, zero_mul]) (by simp),
    Matrix.mul_single_apply_same, mul_one] at h0
  exact (mul_eq_zero.1 h0).resolve_right hne

end GlobalTheory.ParabConj
