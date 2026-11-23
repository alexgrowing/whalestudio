import Formalism.HermitianCurvature.StatementK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecText

namespace Formalism.FourierDecayAlt.P.K

open Matrix Finset Real Formalism.FourierDecayAlt.K

variable {K : Type} [Field K] {n : ℕ}

theorem diag_mul {a b : Matrix (Fin n) (Fin n) K} (ha : a.BlockTriangular id)
    (hb : b.BlockTriangular id) (i : Fin n) : (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [ha h, zero_mul]
    · rw [hb h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem upUni_mul {a b : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) (hb : IsUpUni b) :
    IsUpUni (a * b) := ⟨Matrix.BlockTriangular.mul ha.1 hb.1, fun i => by rw [diag_mul ha.1 hb.1, ha.2, hb.2, one_mul]⟩

theorem upUni_det {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : a.det = 1 := by
  rw [Matrix.det_of_upperTriangular ha.1]
  simp [ha.2]

theorem upUni_isUnit {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : IsUnit a.det := by
  rw [upUni_det ha]
  exact isUnit_one

theorem upUni_inv {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : IsUpUni a⁻¹ := by
  haveI := Matrix.invertibleOfIsUnitDet a (upUni_isUnit ha)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular ha.1
  refine ⟨hinv, fun i => ?_⟩
  have h := diag_mul hinv ha.1 i
  rw [Matrix.nonsing_inv_mul _ (upUni_isUnit ha), ha.2, mul_one, Matrix.one_apply_eq] at h
  exact h.symm

theorem antidiag_mul_diagonal (d : Fin n → K) :
    w0 n * diagonal d = Matrix.of fun i j => if i = Fin.rev j then d j else 0 := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [w0, Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  have hiff : ((i : ℕ) + (j : ℕ) + 1 = n) ↔ i = Fin.rev j := by
    rw [Fin.ext_iff, Fin.val_rev]
    omega
  by_cases h : i = Fin.rev j
  · rw [if_pos (hiff.mpr h), if_pos h, one_mul]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, zero_mul]

theorem mulW_apply (a : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (i j : Fin n) :
    (a * (w0 n * diagonal d) : Matrix (Fin n) (Fin n) K) i j = a i (Fin.rev j) * d j := by
  rw [antidiag_mul_diagonal, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Wmul_apply (c : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (i j : Fin n) :
    ((w0 n * diagonal d) * c : Matrix (Fin n) (Fin n) K) i j = d (Fin.rev i) * c (Fin.rev i) j := by
  rw [antidiag_mul_diagonal, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp
  · intro k _ hk
    simp only [Matrix.of_apply]
    rw [if_neg, zero_mul]
    intro h
    apply hk
    rw [h, Fin.rev_rev]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lower_eq_one {a c : Matrix (Fin n) (Fin n) K} {d : Fin n → K} (ha : IsUpUni a)
    (hc : IsUpUni c) (hd : ∀ x, d x ≠ 0)
    (h : a * (w0 n * diagonal d) = (w0 n * diagonal d) * c) : a = 1 := by
  ext i k
  rw [Matrix.one_apply]
  split_ifs with hik
  · subst hik
    exact ha.2 i
  · rcases lt_or_gt_of_ne hik with h' | h'
    · have e := congrFun (congrFun h i) (Fin.rev k)
      rw [mulW_apply, Wmul_apply, Fin.rev_rev] at e
      have hc0 : c (Fin.rev i) (Fin.rev k) = 0 := hc.1 (Fin.rev_lt_rev.mpr h')
      rw [hc0, mul_zero] at e
      exact (mul_eq_zero.mp e).resolve_right (hd _)
    · exact ha.1 h'

theorem right_eq_one {b : Matrix (Fin n) (Fin n) K} {d : Fin n → K} (hd : ∀ x, d x ≠ 0)
    (h : (w0 n * diagonal d) * b = w0 n * diagonal d) : b = 1 := by
  ext x j
  have e := congrFun (congrFun h (Fin.rev x)) j
  have e1 : (w0 n * Matrix.diagonal d : Matrix (Fin n) (Fin n) K) (Fin.rev x) j =
      ((w0 n * Matrix.diagonal d) * 1 : Matrix (Fin n) (Fin n) K) (Fin.rev x) j := by
    rw [Matrix.mul_one]
  rw [e1, Wmul_apply, Wmul_apply, Fin.rev_rev] at e
  exact mul_left_cancel₀ (hd x) e

theorem bigCellFree : BigCellFree := by
  intro K' _ m v v' u u' d hv hv' hu hu' hd h
  have hvU := upUni_isUnit hv
  have hv'U := upUni_isUnit hv'
  rw [Matrix.mul_assoc v (w0 m) (Matrix.diagonal d)] at h
  obtain ⟨W, hW⟩ : ∃ W, W = w0 m * Matrix.diagonal d := ⟨_, rfl⟩
  rw [← hW] at h
  have ha : IsUpUni (v⁻¹ * u * v) := upUni_mul (upUni_mul (upUni_inv hv) hu) hv
  have hc : IsUpUni (v' * u' * v'⁻¹) := upUni_mul (upUni_mul hv' hu') (upUni_inv hv')
  have hcU := upUni_isUnit hc
  have key : (v⁻¹ * u * v) * W * (v' * u' * v'⁻¹) = W := by
    have e : v⁻¹ * (u * (v * W * v') * u') * v'⁻¹ = W := by
      rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hvU, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hv'U, Matrix.mul_one]
    rw [show (v⁻¹ * u * v) * W * (v' * u' * v'⁻¹) = v⁻¹ * (u * (v * W * v') * u') * v'⁻¹ by
      simp only [Matrix.mul_assoc]]
    exact e
  have key2 : (v⁻¹ * u * v) * W = W * (v' * u' * v'⁻¹)⁻¹ := by
    calc (v⁻¹ * u * v) * W
        = (v⁻¹ * u * v) * W * ((v' * u' * v'⁻¹) * (v' * u' * v'⁻¹)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hcU, Matrix.mul_one]
      _ = ((v⁻¹ * u * v) * W * (v' * u' * v'⁻¹)) * (v' * u' * v'⁻¹)⁻¹ :=
          (Matrix.mul_assoc _ _ _).symm
      _ = W * (v' * u' * v'⁻¹)⁻¹ := by rw [key]
  have ha1 : v⁻¹ * u * v = 1 := lower_eq_one ha (upUni_inv hc) hd (by rw [← hW]; exact key2)
  rw [ha1, Matrix.one_mul] at key
  have hc1 : v' * u' * v'⁻¹ = 1 := right_eq_one hd (by rw [← hW]; exact key)
  constructor
  · calc u = v * (v⁻¹ * u * v) * v⁻¹ := by
          simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hvU, Matrix.one_mul]
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hvU, Matrix.mul_one]
      _ = 1 := by rw [ha1, Matrix.mul_one, Matrix.mul_nonsing_inv _ hvU]
  · calc u' = v'⁻¹ * (v' * u' * v'⁻¹) * v' := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hv'U, Matrix.one_mul]
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hv'U, Matrix.mul_one]
      _ = 1 := by rw [hc1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hv'U]

theorem jointTheoremA : JointTheoremA := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.coarseBound
  refine ⟨2 * C₀, C, ?_⟩
  intro Kx Θ f r e σ hKx hf hΘ hr he hσ hrec
  have hΘ1 : 1 ≤ Θ := by linarith
  have hΘpos : 0 < Θ := by linarith
  have ha0 : 0 ≤ C₀ / Θ := div_nonneg (by linarith) hΘpos.le
  have hq : C₀ / Θ ≤ 1 / 2 := by
    rw [div_le_iff₀ hΘpos]
    linarith
  have ha : (C₀ / Θ) ^ f ≤ 1 / 2 := by
    calc (C₀ / Θ) ^ f ≤ (C₀ / Θ) ^ 1 := pow_le_pow_of_le_one ha0 (by linarith) hf
      _ ≤ 1 / 2 := by rw [pow_one]; exact hq
  have hrp : Θ ^ (-(Kx - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ1 (by linarith)
  have hε0 : 0 ≤ C₀ * Θ ^ (-(Kx - 5 / 2)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hΘpos.le _)
  have hεa : (C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (C₀ / Θ) ^ f := by
    apply pow_le_pow_left₀ hε0
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrp (by linarith)
  exact hC r ((C₀ / Θ) ^ f) ((C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f) e σ (pow_nonneg ha0 _) ha
    (pow_nonneg hε0 _) hεa hr he hσ hrec

end Formalism.FourierDecayAlt.P.K

theorem Formalism.FourierDecayAlt.P.big_cell_free : Formalism.FourierDecayAlt.K.BigCellFree := Formalism.FourierDecayAlt.P.K.bigCellFree

theorem Formalism.FourierDecayAlt.P.joint_theorem_A' : Formalism.FourierDecayAlt.K.JointTheoremA := Formalism.FourierDecayAlt.P.K.jointTheoremA
