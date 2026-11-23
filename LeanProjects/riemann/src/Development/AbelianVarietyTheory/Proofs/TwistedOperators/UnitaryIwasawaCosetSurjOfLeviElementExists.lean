import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadical

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem rev_zero_eq_last {N : ℕ} : (0 : Fin (N + 2)).rev = Fin.last (N + 1) := by ext; simp [Fin.val_rev]

theorem rev_last_eq_zero {N : ℕ} : (Fin.last (N + 1)).rev = (0 : Fin (N + 2)) := by ext; simp [Fin.val_rev]

theorem blk_rev_of_eq {N : ℕ} (a b : Fin (N + 2)) (h : blk N a = blk N b) : blk N a.rev = blk N b.rev := by
  rcases idx_cases a with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [rev_zero_eq_last, rev_last_eq_zero, ← mid_rev] at h ⊢

theorem lt_of_blk_lt {N : ℕ} {a b : Fin (N + 2)} (h : blk N a < blk N b) : a < b := by
  rcases idx_cases a with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Fin.lt_def] at h ⊢

theorem cosetSurj_of_leviExists : LeviExists → CosetSurj := by
  intro _ L _ _ ϖ σ q N hU g
  have hσσ : ∀ x, σ (σ x) = x := hU.1
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨b, k, hb, hk, rfl⟩ := P.fIwasawa_iwasawa σ hσσ hσv g
  have hbT : (mat b).BlockTriangular (blk N) := fun i j h => hb i j (lt_of_blk_lt h)
  obtain ⟨m', hm'L, hm'e, hu'⟩ := leviPart L σ (N + 2) (blk N) blk_rev_of_eq b hbT
  set M₀ : Matrix (Fin N) (Fin N) L := Matrix.of fun i j => mat m' (mid i) (mid j) with hM₀
  have hM₀U : cT σ M₀ * antiJ L N * M₀ = antiJ L N := by
    have h1 : cT σ (mat m') * antiJ L (N + 2) * mat m' = antiJ L (N + 2) := m'.2
    ext i j
    have h2 := congrFun (congrFun h1 (mid i)) (mid j)
    rw [Matrix.mul_apply, sum_idx] at h2
    have e0 : mat m' 0 (mid j) = 0 := hm'L _ _ (by simp)
    have eL : mat m' (Fin.last (N + 1)) (mid j) = 0 := hm'L _ _ (by simp)
    rw [e0, eL, mul_zero, mul_zero, zero_add, add_zero] at h2
    have hJ : antiJ L (N + 2) (mid i) (mid j) = antiJ L N i j := by
      simp only [antiJ]
      exact if_congr (by simp only [val_mid]; omega) rfl rfl
    rw [hJ] at h2
    rw [← h2, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [P.fSatake_cTJ, P.fSatake_cTJ, ← mid_rev]
    rfl
  obtain ⟨g₀, hg₀⟩ := exists_mat M₀ hM₀U
  obtain ⟨⟨k₀, hk₀⟩, hout⟩ := QuotientGroup.mk_out_eq_mul (KU σ N) g₀
  have hxL : σ (mat m' 0 0) * mat m' (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by
    rw [hm'e 0 0 rfl, hm'e _ _ rfl]
    have := P.fSatake_unit_diag hb 0
    rwa [rev_zero_eq_last] at this
  have hx0 : mat m' 0 0 ≠ 0 := by
    intro h; rw [h, map_zero, zero_mul] at hxL; exact zero_ne_one hxL
  have hvx0 : Valued.v (mat m' 0 0) ≠ 0 := by simpa using hx0
  have hvx : Valued.v (mat m' 0 0) = WithZero.exp (-(-(Valued.v (mat m' 0 0)).log)) := by
    rw [neg_neg, WithZero.exp_log hvx0]
  refine ⟨-(Valued.v (mat m' 0 0)).log, (g₀ : GU σ N ⧸ KU σ N), fun m hm => ?_⟩
  obtain ⟨hmL, hm0, hmLL, hmM⟩ := hm
  generalize -(Valued.v (mat m' 0 0)).log = a at hvx hm0 hmLL
  have hmiL : m⁻¹ ∈ leviU σ (blk N) := inv_mem hmL
  have hcL : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hmiL hm'L
  have hcK : m⁻¹ * m' ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hσv]
    intro i j
    by_cases hij : blk N i = blk N j
    swap
    · rw [hcL i j hij]; exact zero_mem _
    rw [mat_mul, Matrix.mul_apply, sum_idx]
    rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
      simp at hij
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL 0 (mid l) (by simp), zero_mul]),
        hmiL 0 (Fin.last _) (by simp), zero_mul, add_zero, add_zero, mat_inv_apply, rev_zero_eq_last, hmLL,
        map_zpow₀, hσϖ]
      rw [intL, Valuation.mem_integer_iff]
      rw [map_mul, map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_add,
        show (-a) • (-1 : ℤ) + -a = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
    · rw [hmiL (mid i) 0 (by simp), zero_mul, zero_add, hmiL (mid i) (Fin.last _) (by simp), zero_mul, add_zero]
      have e : ∑ l, mat m⁻¹ (mid i) (mid l) * mat m' (mid l) (mid j) = mat ((g₀ * k₀)⁻¹ * g₀) i j := by
        rw [mat_mul, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, hmM, hout, hg₀]
        rfl
      rw [e, show (g₀ * k₀)⁻¹ * g₀ = k₀⁻¹ by group]
      exact P.fSatake_K_int (inv_mem hk₀) i j
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL (Fin.last _) (mid l) (by simp), zero_mul]),
        hmiL (Fin.last _) 0 (by simp), zero_mul, zero_add, zero_add, mat_inv_apply, rev_last_eq_zero, hm0,
        map_zpow₀, hσϖ, eq_inv_of_mul_eq_one_right hxL, intL, Valuation.mem_integer_iff, map_mul, map_inv₀, hσv,
        map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add,
        show a • (-1 : ℤ) + -(-a) = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
  obtain ⟨hr, -⟩ := leviRad L σ (N + 2) (blk N) hσv (m⁻¹ * m') hcL (m'⁻¹ * b) hu'
  exact ⟨(m⁻¹ * m') * (m'⁻¹ * b) * (m⁻¹ * m')⁻¹, hr, (m⁻¹ * m') * k, mul_mem hcK hk, by group⟩

end GlobalTheory.InertZeta
