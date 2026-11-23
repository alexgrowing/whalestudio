import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.HolDS

theorem posDef_one_sub_of_sum_sq_lt {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix m n ℂ)
    (h : ∑ i, ∑ j, ‖M i j‖ ^ 2 < 1) : (1 - Mᴴ * M).PosDef := by
  have key : ∀ {k : Type} [Fintype k] (v : k → ℂ), star v ⬝ᵥ v = ((∑ a, ‖v a‖ ^ 2 : ℝ) : ℂ) := by
    intro k _ v
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum,
      Complex.ofReal_pow]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self M)) fun x hx => ?_
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec, key, key, ← Complex.ofReal_sub, Complex.zero_lt_real]
  have hpos : 0 < ∑ a, ‖x a‖ ^ 2 := by
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hx
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨a, Finset.mem_univ _, by
      have : 0 < ‖x a‖ := norm_pos_iff.2 ha
      positivity⟩
  have hle : ∑ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ (∑ i, ∑ j, ‖M i j‖ ^ 2) * ∑ a, ‖x a‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M i j‖) (fun j => ‖x j‖))
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  nlinarith

theorem exists_congr_one_of_posDef {n : Type} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ} (h : S.PosDef) :
    ∃ d : Matrix n n ℂ, IsUnit d.det ∧ dᴴ * S * d = 1 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 h.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  have hd : B.det ≠ 0 := by
    have h2 := h.det_pos.ne'
    rw [hB, Matrix.det_mul] at h2
    exact right_ne_zero_of_mul h2
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det _ hd.isUnit, ?_⟩
  rw [hB, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd.isUnit]
  simp

theorem exists_inU_zOf_eq {p q : ℕ} (Z : Fin p × Fin q → ℂ) (h : ∑ i, ∑ j, ‖Z (i, j)‖ ^ 2 < 1) :
    ∃ x : Mat p q, InU x ∧ zOf x = Z := by
  set M : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun i j => Z (i, j) with hM
  obtain ⟨d, hd, hd1⟩ := exists_congr_one_of_posDef (posDef_one_sub_of_sum_sq_lt M h)
  obtain ⟨a, -, ha1⟩ := exists_congr_one_of_posDef (posDef_one_sub_of_sum_sq_lt Mᴴ (by
    rw [Finset.sum_comm]
    simpa [hM] using h))
  rw [Matrix.conjTranspose_conjTranspose] at ha1
  refine ⟨Matrix.fromBlocks a (M * d) (Mᴴ * a) d, ?_, ?_⟩
  · unfold InU
    rw [Jm_eq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc] at ha1 hd1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← ha1]; abel
    · abel
    · abel
    · rw [← hd1]; abel
  · funext ij
    simp only [zOf, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    rfl

theorem eq_zero_of_eval_zOf (p q : ℕ) (P : PolB p q)
    (h : ∀ x : Mat p q, InU x → MvPolynomial.eval (zOf x) P = 0) : P = 0 := by
  set e : ℝ := 1 / ((p : ℝ) * q + 1) with he
  have hpq : (0 : ℝ) ≤ (p : ℝ) * q := by positivity
  have he0 : 0 < e := by positivity
  have he1 : e * ((p : ℝ) * q + 1) = 1 := by rw [he]; field_simp
  have hele : e ≤ 1 := by nlinarith
  refine MvPolynomial.funext_set (fun _ => Metric.ball (0 : ℂ) e)
    (fun _ => infinite_of_mem_nhds (0 : ℂ) (Metric.ball_mem_nhds _ he0)) fun Z hZ => ?_
  have hZ' : ∀ ij, ‖Z ij‖ ^ 2 ≤ e := fun ij => by
    have h1 : ‖Z ij‖ < e := by simpa using hZ ij (Set.mem_univ _)
    have := norm_nonneg (Z ij)
    nlinarith
  obtain ⟨x, hx, rfl⟩ := exists_inU_zOf_eq Z (by
    calc _ ≤ ∑ _i : Fin p, ∑ _j : Fin q, e :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hZ' _
      _ = (p : ℝ) * q * e := by simp [mul_assoc]
      _ < 1 := by nlinarith)
  rw [h x hx, map_zero]

end GlobalTheory.HolDS
