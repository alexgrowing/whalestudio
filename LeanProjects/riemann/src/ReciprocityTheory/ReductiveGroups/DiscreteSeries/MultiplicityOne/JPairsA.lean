import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateNormInequalities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : gN g = ‖g‖ := by
  rw [frobenius_norm_def, gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem gN_mul_le {k r : ℕ} (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact frobenius_norm_mul A B

theorem gN_conjTranspose {k r : ℕ} (A : Mat k r) : gN Aᴴ = gN A := by
  rw [gN_eq_frob, gN_eq_frob, frobenius_norm_conjTranspose]

end frob

theorem gN_nonneg {k r : ℕ} (A : Mat k r) : 0 ≤ gN A := Real.sqrt_nonneg _

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [Hpk_out k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [Hpk_mid k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  ext i
  rw [Hpk_mulVec]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, Hpk_mulVec]
    have e1 : ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val) = 2 * r + k - i.val := rfl
    rw [if_pos (by rw [e1]; omega)]
    congr 1; ext; simp; omega
  · rw [if_neg h1, Hpk_mulVec, if_neg h1]
    split_ifs <;> simp

theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' k r fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]

theorem UH_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

theorem GV_mul {g x : Mat k r} (hg : g ∈ GV k r) (hx : x ∈ GV k r) : g * x ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

end hpk

theorem gN_le_mul {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) (x : Mat k r) :
    gN x ≤ gN (Hpk k r) ^ 2 * (gN g * gN (g * x)) := by
  have hx : x = Hpk k r * gᴴ * Hpk k r * (g * x) := by
    rw [← Matrix.mul_assoc, UH_left_inv k r hg, Matrix.one_mul]
  have h0 := gN_nonneg (Hpk k r)
  calc gN x = gN (Hpk k r * gᴴ * Hpk k r * (g * x)) := by rw [← hx]
    _ ≤ gN (Hpk k r * gᴴ * Hpk k r) * gN (g * x) := gN_mul_le _ _
    _ ≤ gN (Hpk k r) * gN g * gN (Hpk k r) * gN (g * x) := by
        gcongr
        · exact gN_nonneg _
        · calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le _ _
            _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) := by gcongr; exact gN_mul_le _ _
            _ = gN (Hpk k r) * gN g * gN (Hpk k r) := by rw [gN_conjTranspose]
    _ = gN (Hpk k r) ^ 2 * (gN g * gN (g * x)) := by ring

theorem real_key {A B X c a b : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hX : 0 < X) (hc : 0 < c) (hb : 0 ≤ b)
    (hab : b ≤ a) (hXle : X ≤ c * (B * A)) :
    A ^ (-a) * B ^ (-a) ≤ (X * c⁻¹) ^ (-(a - b)) * B ^ (-b) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hP : 0 < B * A := mul_pos hB0 hA0
  have e1 : A ^ (-a) * B ^ (-a) = (B * A) ^ (-(a - b)) * (B * A) ^ (-b) := by
    rw [← Real.rpow_add hP, Real.mul_rpow hB0.le hA0.le, mul_comm]; ring_nf
  rw [e1]
  have hXc : 0 < X * c⁻¹ := mul_pos hX (inv_pos.2 hc)
  have h1 : (B * A) ^ (-(a - b)) ≤ (X * c⁻¹) ^ (-(a - b)) := by
    refine Real.rpow_le_rpow_of_nonpos hXc ?_ (by linarith)
    rw [mul_inv_le_iff₀ hc]; linarith [hXle]
  have h2 : (B * A) ^ (-b) ≤ B ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos hB0 (by nlinarith) (by linarith)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg hXc.le _)

theorem AB_le_AG (k r : ℕ) : AB k r ≤ AG k r + 1 := by
  simp only [AB, AG, nR]
  push_cast
  nlinarith [sq_nonneg ((k : ℝ) + r - (r + 1)), (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
    (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

end ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateNormInequalities
