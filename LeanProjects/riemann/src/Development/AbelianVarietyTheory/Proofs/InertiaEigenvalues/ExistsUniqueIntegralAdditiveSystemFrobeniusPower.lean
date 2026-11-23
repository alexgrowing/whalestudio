import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm

open GlobalTheory.PMonE Finset

namespace GlobalTheory.PMonE

theorem gsum_sub_of_charP {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] {m : Type*} [Fintype m]
    (e D : ℕ) (M : ℕ → Matrix m m F) (x y : m → F) :
    gsum (p ^ e) D M (x - y) = gsum (p ^ e) D M x - gsum (p ^ e) D M y := by
  unfold gsum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply, ← pow_mul]
  exact sub_pow_char_pow _ _ _

theorem norm_gsum_le_of_small {F : Type*} [NormedField F] [IsUltrametricDist F] {m : Type*} [Fintype m]
    (q D : ℕ) (hq : 0 < q) (M : ℕ → Matrix m m F) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ n, n ≤ D → ∀ i j, ‖M n i j‖ ≤ δ) (z : m → F) (hz : ‖z‖ ≤ 1) :
    ‖gsum q D M z‖ ≤ δ * ‖z‖ := by
  have h0 : 0 ≤ δ * ‖z‖ := mul_nonneg hδ (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg h0]
  intro i
  unfold gsum
  rw [Finset.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun n hn => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun j _ => ?_
  rw [norm_mul, norm_pow]
  have hj : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
  refine mul_le_mul (hM n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) i j) ?_ (by positivity) hδ
  exact (pow_le_of_le_one (norm_nonneg _) (hj.trans hz) (pow_pos hq n).ne').trans hj

theorem gsum_eq_add_gsum_update {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
    (q D : ℕ) (U : ℕ → Matrix m m F) (y : m → F) :
    gsum q D U y = y + gsum q D (fun n => if n = 0 then U 0 - 1 else U n) y := by
  unfold gsum
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp [Matrix.sub_mulVec]
  abel

theorem existsUnique_integral_gsum_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ) (_he : 0 < e)
    (U : ℕ → Matrix m m F) (h0 : ∀ i j, ‖(U 0 - 1) i j‖ < 1) (h1 : ∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1)
    (b : m → F) (hb : Integral b) : ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by
  set V : ℕ → Matrix m m F := fun n => if n = 0 then U 0 - 1 else U n with hV
  have hVs : ∀ n i j, ‖V n i j‖ < 1 := by
    intro n i j
    by_cases hn : n = 0
    · simpa [hV, hn] using h0 i j
    · simpa [hV, hn] using h1 n (Nat.one_le_iff_ne_zero.mpr hn) i j
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ : NNReal, δ < 1 ∧ ∀ n, n ≤ D → ∀ i j, ‖V n i j‖ ≤ δ := by
    refine ⟨((range (D + 1)) ×ˢ (univ : Finset (m × m))).sup fun t => ‖V t.1 t.2.1 t.2.2‖₊, ?_, ?_⟩
    · rw [Finset.sup_lt_iff (by simp)]
      intro t _
      exact_mod_cast hVs t.1 t.2.1 t.2.2
    · intro n hn i j
      have := Finset.le_sup (f := fun t : ℕ × m × m => ‖V t.1 t.2.1 t.2.2‖₊)
        (s := (range (D + 1)) ×ˢ (univ : Finset (m × m))) (b := (n, i, j))
        (by simp [Nat.lt_succ_iff, hn])
      exact_mod_cast this
  have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hint : ∀ y : m → F, Integral y ↔ ‖y‖ ≤ 1 := fun y => (pi_norm_le_iff_of_nonneg zero_le_one).symm
  have hbound := norm_gsum_le_of_small (p ^ e) D hq V δ δ.2 hδ
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hsub : ∀ x y : m → F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x - y‖ ≤ 1 := by
    intro x y hx hy
    rw [← hint] at *
    intro i
    rw [Pi.sub_apply, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) ?_)
    rw [norm_neg]; exact hy i
  let T : (m → F) → (m → F) := fun y => b - gsum (p ^ e) D V y
  let S : Set (m → F) := Metric.closedBall 0 1
  have hS : ∀ y, y ∈ S ↔ ‖y‖ ≤ 1 := fun y => mem_closedBall_zero_iff
  have hT : ∀ x y : m → F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖T x - T y‖ ≤ δ * ‖x - y‖ := by
    intro x y hx hy
    have : T x - T y = - gsum (p ^ e) D V (x - y) := by
      rw [gsum_sub_of_charP]; simp only [T]; abel
    rw [this, norm_neg]
    exact hbound _ (hsub x y hx hy)
  have hmaps : Set.MapsTo T S S := by
    intro y hy
    rw [hS] at hy ⊢
    refine hsub _ _ ((hint b).mp hb) ((hbound y hy).trans ?_)
    exact mul_le_one₀ hδ1'.le (norm_nonneg _) hy
  have hc : ContractingWith δ (hmaps.restrict T S S) := by
    refine ⟨hδ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hT x y ((hS _).mp x.2) ((hS _).mp y.2)
  have hfix : ∀ y, gsum (p ^ e) D U y = b ↔ T y = y := by
    intro y
    rw [gsum_eq_add_gsum_update]
    simp only [T]
    constructor
    · intro h; rw [← h]; simp [hV]
    · intro h; rw [sub_eq_iff_eq_add] at h; exact h.symm
  obtain ⟨y, hyS, hy, -⟩ := hc.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps
    (x := 0) ((hS 0).mpr (by simp)) (edist_ne_top _ _)
  refine ⟨y, ⟨(hint y).mpr ((hS y).mp hyS), (hfix y).mpr hy⟩, ?_⟩
  rintro x ⟨hx, hx'⟩
  have h := hT x y ((hint x).mp hx) ((hS y).mp hyS)
  rw [(hfix x).mp hx', show T y = y from hy] at h
  have hn := norm_nonneg (x - y)
  have : ‖x - y‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end GlobalTheory.PMonE
