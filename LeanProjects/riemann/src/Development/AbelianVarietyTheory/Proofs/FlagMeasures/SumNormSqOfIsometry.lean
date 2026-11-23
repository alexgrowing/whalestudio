import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace

open Formalism.REAL Matrix

namespace GlobalTheory.OnbSum

theorem conjTranspose_eq_of_inG {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : inG ε X) : Xᴴ = -(Jm ε * X * Jm ε) := by
  have h' : Xᴴ * Jm ε + Jm ε * X = 0 := h
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h'
  calc Xᴴ = Xᴴ * (Jm ε * Jm ε) := by rw [Jm_mul_self, Matrix.mul_one]
    _ = Xᴴ * Jm ε * Jm ε := (Matrix.mul_assoc _ _ _).symm
    _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]

theorem trace_im_eq_zero {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : (Matrix.trace (A * Bᴴ)).im = 0 := by
  have hA' := conjTranspose_eq_of_inG hA
  have hB' := conjTranspose_eq_of_inG hB
  have swap : Matrix.trace (B * Aᴴ) = Matrix.trace (A * Bᴴ) := by
    rw [hA', hB', Matrix.mul_neg, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_neg, neg_inj]
    calc Matrix.trace (B * (Jm ε * A * Jm ε)) = Matrix.trace ((B * Jm ε * A) * Jm ε) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Jm ε * (B * Jm ε * A)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Jm ε * B * Jm ε) * A) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (A * (Jm ε * B * Jm ε)) := Matrix.trace_mul_comm _ _
  have hstar : (starRingEnd ℂ) (Matrix.trace (A * Bᴴ)) = Matrix.trace (A * Bᴴ) := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, swap]
  exact Complex.conj_eq_iff_im.mp hstar

theorem sum_norm_sq_of_isometry {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Matrix ι κ ℂ) (hM : Mᴴ * M = 1)
    (y : κ → V) : ∑ i, ‖∑ p, M i p • y p‖ ^ 2 = ∑ p, ‖y p‖ ^ 2 := by
  have key : ∀ p q, ∑ i, (starRingEnd ℂ) (M i p) * M i q = if p = q then (1 : ℂ) else 0 := by
    intro p q
    have h := congrFun (congrFun hM p) q
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa only [Matrix.conjTranspose_apply, Complex.star_def] using h
  have hsq : ∀ v : V, (‖v‖ : ℂ) ^ 2 = inner ℂ v v := fun v => (inner_self_eq_norm_sq_to_K v).symm
  have expand : ∀ i, inner ℂ (∑ p, M i p • y p) (∑ q, M i q • y q) =
      ∑ p, ∑ q, (starRingEnd ℂ) (M i p) * M i q * inner ℂ (y p) (y q) := by
    intro i
    rw [sum_inner]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [inner_smul_left, inner_smul_right, mul_assoc]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [hsq, expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, key]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem onb_sum : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (y : Fin n → Fin n → V), (∀ F : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsONFamily ε F → ∑ i, ‖∑ a, ∑ b, F i a b • y a b‖ ^ 2 = ∑ a, ∑ b, ‖y a b‖ ^ 2) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖∑ a, ∑ b, X a b • y a b‖ ^ 2 ≤ hs X * ∑ a, ∑ b, ‖y a b‖ ^ 2 := by
  intro n ε V _ _ y
  refine ⟨fun F hF => ?_, fun X => ?_⟩
  · let M : Matrix (Fin (n ^ 2)) (Fin n × Fin n) ℂ := fun i p => F i p.1 p.2
    have hrow : M * Mᴴ = 1 := by
      ext i j
      have hre := hF.2 i j
      have him := trace_im_eq_zero (hF.1 i) (hF.1 j)
      have htr : Matrix.trace (F i * (F j)ᴴ) = (M * Mᴴ) i j := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
        rw [Fintype.sum_prod_type]
      rw [← htr, Matrix.one_apply]
      apply Complex.ext
      · rw [hre]; split_ifs <;> simp
      · rw [him]; split_ifs <;> simp
    have e : Fin n × Fin n ≃ Fin (n ^ 2) := Fintype.equivOfCardEq (by simp [sq])
    have hcol : Mᴴ * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mp hrow
    have hiso := sum_norm_sq_of_isometry M hcol (fun p => y p.1 p.2)
    simpa only [M, Fintype.sum_prod_type] using hiso
  · have h1 : ‖∑ a, ∑ b, X a b • y a b‖ ≤ ∑ a, ∑ b, ‖X a b‖ * ‖y a b‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_smul (X a b) (y a b)).le))
    have h2 : (∑ a, ∑ b, ‖X a b‖ * ‖y a b‖) ^ 2 ≤ hs X * ∑ a, ∑ b, ‖y a b‖ ^ 2 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
        (fun p => ‖X p.1 p.2‖) (fun p => ‖y p.1 p.2‖)
      simpa only [hs, Fintype.sum_prod_type] using hcs
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

end GlobalTheory.OnbSum
