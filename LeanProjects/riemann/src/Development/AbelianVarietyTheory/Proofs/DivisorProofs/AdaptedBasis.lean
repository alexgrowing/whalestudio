import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

def intSubring (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp [AddValuation.map_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by simp [AddValuation.map_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, AddValuation.map_neg] at *
    exact ha

theorem isIntV_iff (v : AddValuation C (WithTop ℝ)) (x : C) : IsIntV v x ↔ x ∈ intSubring v :=
  Iff.rfl

theorem int_of_le (v : AddValuation C (WithTop ℝ)) {a b : C} (hb : b ≠ 0)
    (h : v b ≤ v (a * b)) : IsIntV v a := by
  show 0 ≤ v a
  rw [AddValuation.map_mul] at h
  have hb' : v b ≠ ⊤ := fun h' => hb ((AddValuation.top_iff v).1 h')
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hb'
  rcases eq_or_ne (v a) ⊤ with ha | ha
  · rw [ha]; exact le_top
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ha
  rw [← hr, ← hs, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  rw [← hs]
  exact_mod_cast (by linarith : (0 : ℝ) ≤ s)

end

end GlobalTheory.LowU

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

def Reduces (v : AddValuation C (WithTop ℝ)) {i n : ℕ} (M : Matrix (Fin i) (Fin n) C) : Prop :=
  ∃ (g : Matrix (Fin i) (Fin i) C) (cr : ℕ), cr ≤ i ∧ cr ≤ n ∧ (∀ a b, IsIntV v (g a b)) ∧
    v g.det = 0 ∧ ∀ a : Fin i, cr ≤ a.val → ∀ e, (g * M) a e = 0

theorem pivot_step (v : AddValuation C (WithTop ℝ)) {i' n : ℕ}
    (ih : ∀ M' : Matrix (Fin i') (Fin n) C, Reduces v M')
    (M : Matrix (Fin (i' + 1)) (Fin (n + 1)) C) (h0 : M 0 0 ≠ 0)
    (hmin : ∀ b, v (M 0 0) ≤ v (M b 0)) : Reduces v M := by
  have hq : ∀ c : Fin i', IsIntV v (M c.succ 0 / M 0 0) := fun c =>
    int_of_le v h0 (by rw [div_mul_cancel₀ _ h0]; exact hmin c.succ)
  obtain ⟨g', cr', hc1, hc2, hint, hdet, hz⟩ :=
    ih (Matrix.of fun c e' => M c.succ e'.succ - M c.succ 0 / M 0 0 * M 0 e'.succ)
  have hw : ∀ a'', IsIntV v (-∑ c, g' a'' c * (M c.succ 0 / M 0 0)) := fun a'' =>
    (isIntV_iff v _).2 (neg_mem (Subring.sum_mem _ fun c _ =>
      mul_mem ((isIntV_iff v _).1 (hint a'' c)) ((isIntV_iff v _).1 (hq c))))
  refine ⟨Matrix.of fun a b => Fin.cases (motive := fun _ => C)
      (Fin.cases (motive := fun _ => C) 1 (fun _ => 0) b)
      (fun a'' => Fin.cases (motive := fun _ => C) (-∑ c, g' a'' c * (M c.succ 0 / M 0 0))
        (fun b'' => g' a'' b'') b) a,
    cr' + 1, by omega, by omega, ?_, ?_, ?_⟩
  · intro a b
    cases a using Fin.cases <;> cases b using Fin.cases <;>
      simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    · simp [IsIntV]
    · simp [IsIntV]
    · exact hw _
    · exact hint _ _
  · have hsub : (Matrix.of fun a b => Fin.cases (motive := fun _ => C)
        (Fin.cases (motive := fun _ => C) 1 (fun _ => 0) b)
        (fun a'' => Fin.cases (motive := fun _ => C) (-∑ c, g' a'' c * (M c.succ 0 / M 0 0))
          (fun b'' => g' a'' b'') b) a).submatrix Fin.succ Fin.succ = g' := by
      ext a b
      simp
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, Fin.succAbove_zero, hsub,
      mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
    exact hdet
  · intro a ha e
    obtain ⟨a'', rfl⟩ := Fin.exists_succ_eq.2 (show a ≠ 0 by rintro rfl; simp at ha)
    have ha' : cr' ≤ a''.val := by rw [Fin.val_succ] at ha; omega
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    cases e using Fin.cases with
    | zero =>
      rw [neg_mul, Finset.sum_mul, neg_add_eq_zero]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_assoc, div_mul_cancel₀ _ h0]
    | succ e' =>
      have h1 := hz a'' ha' e'
      simp only [Matrix.mul_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib] at h1
      have e1 : ∑ c, g' a'' c * (M c.succ 0 / M 0 0 * M 0 e'.succ) =
          (∑ c, g' a'' c * (M c.succ 0 / M 0 0)) * M 0 e'.succ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [e1] at h1
      linear_combination h1

end

end GlobalTheory.LowU

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

theorem one_int (v : AddValuation C (WithTop ℝ)) {i : ℕ} (a b : Fin i) :
    IsIntV v ((1 : Matrix (Fin i) (Fin i) C) a b) := by
  show 0 ≤ v _
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

theorem reduces_all (v : AddValuation C (WithTop ℝ)) :
    ∀ (n i : ℕ) (M : Matrix (Fin i) (Fin n) C), Reduces v M := by
  intro n
  induction n with
  | zero =>
    intro i M
    exact ⟨1, 0, Nat.zero_le _, le_rfl, one_int v, by simp, fun a _ e => e.elim0⟩
  | succ n ih =>
    intro i M
    cases i with
    | zero => exact ⟨1, 0, le_rfl, Nat.zero_le _, one_int v, by simp, fun a _ => a.elim0⟩
    | succ i' =>
      obtain ⟨b0, -, hb0⟩ :=
        Finset.univ.exists_min_image (fun b => v (M b 0)) Finset.univ_nonempty
      by_cases h0 : M b0 0 = 0
      · have hcol : ∀ b, M b 0 = 0 := fun b => by
          have hb := hb0 b (Finset.mem_univ _)
          rw [h0, AddValuation.map_zero, top_le_iff] at hb
          exact (AddValuation.top_iff v).1 hb
        obtain ⟨g, cr, h1, h2, hint, hdet, hz⟩ := ih (i' + 1) (Matrix.of fun a e => M a e.succ)
        refine ⟨g, cr, h1, by omega, hint, hdet, fun a ha e => ?_⟩
        cases e using Fin.cases with
        | zero => simp [Matrix.mul_apply, hcol]
        | succ e' => simpa [Matrix.mul_apply] using hz a ha e'
      · obtain ⟨g1, cr, h1, h2, hint, hdet, hz⟩ := pivot_step v (ih i')
          (M.submatrix (Equiv.swap 0 b0) id) (by simpa using h0)
          (fun b => by simpa using hb0 _ (Finset.mem_univ _))
        refine ⟨g1.submatrix id (Equiv.swap 0 b0), cr, h1, h2, fun a b => hint _ _, ?_,
          fun a ha e => ?_⟩
        · rw [Matrix.det_permute', AddValuation.map_mul, hdet, add_zero]
          rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (i' + 1)) b0)) with
            h | h <;> simp [h]
        · have key : ∑ b, g1 a (Equiv.swap 0 b0 b) * M b e =
              ∑ b, g1 a b * M (Equiv.swap 0 b0 b) e := by
            rw [← Equiv.sum_comp (Equiv.swap 0 b0) (fun b => g1 a b * M (Equiv.swap 0 b0 b) e)]
            simp [Equiv.swap_apply_self]
          simpa [Matrix.mul_apply, key] using hz a ha e

end

end GlobalTheory.LowU

theorem GlobalTheory.LowU.adapted_basis : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (i d : ℕ) (u : Fin i → Fin d → C) (S : Finset (Fin d)), IsSatFrame v u →
    ∃ (g : Matrix (Fin i) (Fin i) C) (cr : ℕ), cr ≤ i ∧ cr ≤ S.card ∧ (∀ a b, IsIntV v (g a b)) ∧
      v g.det = 0 ∧ ∀ a : Fin i, cr ≤ a.val → ∀ e ∈ S, ∑ a', g a a' * u a' e = 0 := by
  intro C _ _ v i d u S _
  obtain ⟨g, cr, h1, h2, hint, hdet, hz⟩ := GlobalTheory.LowU.reduces_all v S.card i
    (Matrix.of fun a k => u a (S.equivFin.symm k))
  refine ⟨g, cr, h1, h2, hint, hdet, fun a ha e he => ?_⟩
  simpa [Matrix.mul_apply] using hz a ha (S.equivFin ⟨e, he⟩)
