import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCard

open Finset Formalism.L2.SG.DensExact

namespace PI.DensSplitW

noncomputable def phiX {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (X : Fin m → Fin n → K) : (Fin n → K) →ₗ[K] (Fin m → K) :=
  Matrix.mulVecLin (Matrix.of X * Ph)

theorem phiX_apply {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (X : Fin m → Fin n → K) (y : Fin n → K) (i : Fin m) :
    phiX Ph X y i = ∑ k, ∑ l, X i k * Ph k l * y l := by
  simp only [phiX, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.of_apply]
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem cond_iff {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (Gm : Matrix (Fin m) (Fin m) K) (X Y : Fin m → Fin n → K) :
    (∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j) ↔ ∀ j, phiX Ph X (Y j) = Gm.transpose j := by
  constructor
  · intro h j
    funext i
    rw [phiX_apply, Matrix.transpose_apply]
    exact h i j
  · intro h i j
    have := congrFun (h j) i
    rwa [phiX_apply, Matrix.transpose_apply] at this

theorem phiX_finrank_range {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Module.finrank K (LinearMap.range (phiX Ph X)) = m := by
  have h1 : (Matrix.of X * Ph).rank = m := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det Ph _ hPh, Matrix.rank_eq_finrank_span_row]
    exact (finrank_span_eq_card hX).trans (Fintype.card_fin m)
  exact h1

theorem phiX_surj {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Function.Surjective (phiX Ph X) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [phiX_finrank_range Ph hPh X hX, Module.finrank_fin_fun]

theorem phiX_finrank_ker {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Module.finrank K (LinearMap.ker (phiX Ph X)) = n - m := by
  have h := LinearMap.finrank_range_add_finrank_ker (phiX Ph X)
  rw [phiX_finrank_range Ph hPh X hX, Module.finrank_fin_fun] at h
  omega

theorem count_eq (hF : FiberCard) (K : Type) [Field K] [Fintype K] (n m : ℕ)
    (Ph : Matrix (Fin n) (Fin n) K) (Gm : Matrix (Fin m) (Fin m) K) (hPh : IsUnit Ph.det) :
    countSplit K n m Ph Gm = Nat.card {X : Fin m → Fin n → K // LinearIndependent K X} *
      (Fintype.card K ^ (Gm.rank * (n - m)) *
        ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i)) := by
  classical
  have hfib : ∀ X : {X : Fin m → Fin n → K // LinearIndependent K X},
      Nat.card {Y : Fin m → Fin n → K // LinearIndependent K Y ∧
        ∀ i j, ∑ k, ∑ l, X.1 i k * Ph k l * Y j l = Gm i j} =
      Fintype.card K ^ (Gm.rank * (n - m)) *
        ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i) := by
    intro X
    have e : {Y : Fin m → Fin n → K // LinearIndependent K Y ∧
          ∀ i j, ∑ k, ∑ l, X.1 i k * Ph k l * Y j l = Gm i j} ≃
        {Y : Fin m → Fin n → K // LinearIndependent K Y ∧ ∀ j, phiX Ph X.1 (Y j) = Gm.transpose j} :=
      Equiv.subtypeEquivRight (fun Y => and_congr_right_iff.mpr (fun _ => cond_iff Ph Gm X.1 Y))
    rw [Nat.card_congr e, hF K (Fin n → K) (Fin m → K) (phiX Ph X.1) (phiX_surj Ph hPh X.1 X.2)
      m Gm.transpose, phiX_finrank_ker Ph hPh X.1 X.2]
    have hr : Module.finrank K (Submodule.span K (Set.range (Gm.transpose : Fin m → Fin m → K))) =
        Gm.rank := by
      rw [Matrix.rank_eq_finrank_span_cols]
      rfl
    rw [hr]
  unfold countSplit
  rw [← Nat.card_coe_set_eq]
  have e2 : ↥{XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
        LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j} ≃
      Σ X : {X : Fin m → Fin n → K // LinearIndependent K X},
        {Y : Fin m → Fin n → K // LinearIndependent K Y ∧
          ∀ i j, ∑ k, ∑ l, X.1 i k * Ph k l * Y j l = Gm i j} :=
    { toFun := fun s =>
        have hs : LinearIndependent K s.1.1 ∧ LinearIndependent K s.1.2 ∧
            ∀ i j, ∑ k, ∑ l, s.1.1 i k * Ph k l * s.1.2 j l = Gm i j := s.2
        ⟨⟨s.1.1, hs.1⟩, ⟨s.1.2, hs.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), by exact ⟨s.1.2, s.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e2, Nat.card_sigma, Finset.sum_congr rfl (fun X _ => hfib X),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem sub_factor (q N i : ℕ) (hq : 0 < q) (hi : i ≤ N) :
    ((q ^ N - q ^ i : ℕ) : ℝ) = (q : ℝ) ^ N * (1 - ((q : ℝ) ^ (N - i))⁻¹) := by
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq hi), Nat.cast_pow, Nat.cast_pow]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h : (q : ℝ) ^ N = (q : ℝ) ^ i * (q : ℝ) ^ (N - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  have hne : (q : ℝ) ^ (N - i) ≠ 0 := by positivity
  rw [h]
  field_simp

theorem prod_factor (q b c : ℕ) (hq : 0 < q) (hc : c ≤ b) :
    ((∏ i ∈ range c, (q ^ b - q ^ i) : ℕ) : ℝ) =
      (q : ℝ) ^ (b * c) * ∏ i ∈ range c, (1 - ((q : ℝ) ^ (b - i))⁻¹) := by
  rw [Nat.cast_prod]
  rw [Finset.prod_congr rfl (fun i hi => sub_factor q b i hq
    (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hc)))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]

theorem exp_eq (n m r : ℕ) (hmn : m ≤ n) (hrm : r ≤ m) :
    n * m + r * (n - m) + (n - m) * (m - r) = 2 * n * m - m ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hrm
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  apply (Nat.sub_eq_of_eq_add _).symm
  ring

theorem densExactSplit_of (hF : FiberCard) : DensExactSplit := by
  intro K _ _ n m Ph Gm hPh
  rw [count_eq hF K n m Ph Gm hPh]
  have hrm : Gm.rank ≤ m := Matrix.rank_le_width Gm
  have hq0 : 0 < Fintype.card K := Fintype.card_pos
  have hqR : (0 : ℝ) < Fintype.card K := by exact_mod_cast hq0
  by_cases hmc : m + (m - Gm.rank) ≤ n
  · have hmn : m ≤ n := by omega
    rw [card_linearIndependent (K := K) (V := Fin n → K) (by rw [Module.finrank_fin_fun]; exact hmn),
      Module.finrank_fin_fun]
    rw [← densSplitDisplay_holds (Fintype.card K) n m (m - Gm.rank) hq0 hmc]
    rw [Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ n - Fintype.card K ^ i) m]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
      prod_factor _ n m hq0 hmn, prod_factor _ (n - m) (m - Gm.rank) hq0 (by omega)]
    have hD : (Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2) =
        (Fintype.card K : ℝ) ^ (2 * n * m - m ^ 2) := by
      rw [pow_sub₀ _ hqR.ne' (by nlinarith : m ^ 2 ≤ 2 * n * m), div_eq_mul_inv]
    rw [hD, ← exp_eq n m Gm.rank hmn hrm]
    rw [pow_add, pow_add]
    have h1 : (Fintype.card K : ℝ) ^ (n * m) ≠ 0 := by positivity
    have h2 : (Fintype.card K : ℝ) ^ (Gm.rank * (n - m)) ≠ 0 := by positivity
    have h3 : (Fintype.card K : ℝ) ^ ((n - m) * (m - Gm.rank)) ≠ 0 := by positivity
    field_simp
  · have hR : densProd (Fintype.card K) 1 n m (m - Gm.rank) = 0 := by
      unfold densProd
      apply Finset.prod_eq_zero (i := 0)
      · simp only [Finset.mem_Icc]; omega
      · simp
    rw [hR]
    have hL : Nat.card {X : Fin m → Fin n → K // LinearIndependent K X} *
        (Fintype.card K ^ (Gm.rank * (n - m)) *
          ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i)) = 0 := by
      by_cases hmn : m ≤ n
      · have : ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i) = 0 :=
          Finset.prod_eq_zero (i := n - m) (Finset.mem_range.mpr (by omega)) (by simp)
        rw [this, mul_zero, mul_zero]
      · have : IsEmpty {X : Fin m → Fin n → K // LinearIndependent K X} := by
          refine ⟨fun X => ?_⟩
          have := X.2.fintype_card_le_finrank
          simp only [Fintype.card_fin, Module.finrank_fin_fun] at this
          omega
        rw [Nat.card_of_isEmpty, zero_mul]
    rw [hL]
    simp

end PI.DensSplitW
