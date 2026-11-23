import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Detlow
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hadam

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem diag_eq {N : ℕ} (B H : Matrix (Fin N) (Fin N) ℂ) (a : Fin N) :
    (Bᴴ * H * B) a a = star (fun i => B i a) ⬝ᵥ (H *ᵥ fun i => B i a) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, dotProduct, mulVec]

private theorem det_pull {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (A : Matrix (Fin N) (Fin N) (𝓞 L)) (w : InfinitePlace L) :
    (mat (pull A h) w).det.re = (w (A.det : L)) ^ 2 * (mat h w).det.re := by
  have e : (A.map (embO w)).det = embO w A.det := ((embO w).map_det A).symm
  have e2 : ‖embO w A.det‖ = w (A.det : L) := InfinitePlace.norm_embedding_eq w _
  rw [mat_pull, det_mul, det_mul, det_conjTranspose, e, ← e2]
  have : star (embO w A.det) * (mat h w).det * embO w A.det
      = ((‖embO w A.det‖ ^ 2 : ℝ) : ℂ) * (mat h w).det := by
    rw [mul_right_comm, Complex.star_def, Complex.conj_mul']; push_cast; rfl
  rw [this, Complex.re_ofReal_mul]

private theorem prod_sq {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] (x : 𝓞 L) :
    ∏ w : InfinitePlace L, (w (x : L)) ^ 2 = ((Algebra.norm ℤ x).natAbs : ℝ) := by
  have h1 := InfinitePlace.prod_eq_abs_norm (x : L)
  have h2 : ∀ w : InfinitePlace L, w.mult = 2 := fun w =>
    InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  simp only [h2] at h1
  rw [h1, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

theorem UpperTheory.V.KT.nrmle :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (h : HS L N) (A : Matrix (Fin N) (Fin N) (𝓞 L)),
    h ∈ Ry L N → ColsMin A h → A.det ≠ 0 →
    nrmDet A ≤ I0 L N ∧ ∀ w, (mat (pull A h) w).PosSemidef ∧ (∀ a, (mat (pull A h) w a a).re ≤ 1) ∧
      1 ≤ (I0 L N : ℝ) * ‖(mat (pull A h) w).det‖ := by
  classical
  intro L _ _ _ N h A hR hC hA
  have hpos : ∀ w, (mat h w).PosSemidef := fun w => (rypos L N hR w).posSemidef
  have hpsd : ∀ w, (mat (pull A h) w).PosSemidef := fun w =>
    (hpos w).conjTranspose_mul_mul_same _
  have hsum : ∀ a, ∑ w, (mat (pull A h) w a a).re = 1 := fun a => by
    rw [← hC a, q, qR]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mat_pull, diag_eq]
    rfl
  have hnn : ∀ w a, 0 ≤ (mat (pull A h) w a a).re := fun w a =>
    (Complex.le_def.1 ((hpsd w).diag_nonneg (i := a))).1
  have hdiag : ∀ w a, (mat (pull A h) w a a).re ≤ 1 := fun w a => by
    rw [← hsum a]
    exact Finset.single_le_sum (f := fun w => (mat (pull A h) w a a).re)
      (fun w _ => hnn w a) (Finset.mem_univ w)
  have hH := fun w => hadam N _ (hpsd w) (hdiag w)
  have hlow := detlow L N h hR
  have hprod : ∏ w, (mat (pull A h) w).det.re = (nrmDet A : ℝ) * ∏ w, (mat h w).det.re := by
    simp only [det_pull]
    rw [Finset.prod_mul_distrib, prod_sq]
    rfl
  have hn1 : (1 : ℝ) ≤ nrmDet A := by
    have : nrmDet A ≠ 0 := by
      unfold nrmDet
      rw [Int.natAbs_ne_zero]
      exact Algebra.norm_ne_zero_iff.2 hA
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hI : (0 : ℝ) ≤ I0 L N := Nat.cast_nonneg _
  set P := ∏ w, (mat h w).det.re with hP
  have hle : ∀ w, (nrmDet A : ℝ) * P ≤ (mat (pull A h) w).det.re := fun w => by
    rw [← hprod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
    exact mul_le_of_le_one_right (hH w).1
      (Finset.prod_le_one (fun v _ => (hH v).1) (fun v _ => (hH v).2.1))
  have hle1 : (nrmDet A : ℝ) * P ≤ 1 := by
    rw [← hprod]
    exact Finset.prod_le_one (fun v _ => (hH v).1) (fun v _ => (hH v).2.1)
  refine ⟨?_, fun w => ⟨hpsd w, hdiag w, ?_⟩⟩
  · have : (nrmDet A : ℝ) ≤ I0 L N := by
      calc (nrmDet A : ℝ) ≤ nrmDet A * (I0 L N * P) := le_mul_of_one_le_right (by linarith) hlow
        _ = I0 L N * (nrmDet A * P) := by ring
        _ ≤ I0 L N := mul_le_of_le_one_right hI hle1
    exact_mod_cast this
  · rw [(hH w).2.2]
    calc (1 : ℝ) ≤ nrmDet A * (I0 L N * P) := one_le_mul_of_one_le_of_one_le hn1 hlow
      _ = I0 L N * (nrmDet A * P) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hle w) hI
