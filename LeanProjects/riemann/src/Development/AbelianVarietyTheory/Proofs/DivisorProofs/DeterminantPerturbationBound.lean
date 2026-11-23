import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem detClose_norm_prod_sub_lt {C : Type} [NormedField C] [IsUltrametricDist C] {ι : Type}
    (s : Finset ι) (f g : ι → C) (hf : ∀ i, ‖f i‖ ≤ 1) (hfg : ∀ i, ‖f i - g i‖ < 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ < 1 := by
  classical
  have hg : ∀ i, ‖g i‖ ≤ 1 := fun i => by
    have : g i = f i + -(f i - g i) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf i) (by rw [norm_neg]; exact (hfg i).le))
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖f a‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ 1 * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ :=
            mul_le_mul_of_nonneg_right (hf a) (norm_nonneg _)
        _ < 1 := by simpa using ih
    · rw [norm_mul, norm_prod]
      calc ‖f a - g a‖ * ∏ i ∈ s, ‖g i‖ ≤ ‖f a - g a‖ * 1 :=
            mul_le_mul_of_nonneg_left (Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hg i))
              (norm_nonneg _)
        _ < 1 := by simpa using hfg a

theorem detClose_norm_sum_lt {C : Type} [NormedField C] [IsUltrametricDist C] {ι : Type}
    (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, ‖f i‖ < 1) : ‖∑ i ∈ s, f i‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem detClose_norm_det_sub_lt {C : Type} [NormedField C] [IsUltrametricDist C] {k : ℕ}
    (B B' : Matrix (Fin k) (Fin k) C) (hB : ∀ i j, ‖B i j‖ ≤ 1)
    (hBB : ∀ i j, ‖B i j - B' i j‖ < 1) : ‖B.det - B'.det‖ < 1 := by
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  apply detClose_norm_sum_lt
  intro σ _
  rw [← mul_sub, norm_mul]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : C)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]
  exact detClose_norm_prod_sub_lt _ _ _ (fun i => hB _ _) (fun i => hBB _ _)

theorem det_sub_lt_of_close_on_unitBall : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] (J : Type) (k : ℕ) (P P' : J → Fin k → C) (N : ℝ), 0 < N → (∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ ≤ N) → (∃ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ = N) → (∀ cf : Fin k → C, (∀ j, ‖∑ l, cf l * P j l‖ ≤ 1) → ∀ j, ‖∑ l, cf l * (P j l - P' j l)‖ < 1) → ∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det - (Matrix.of fun r l => P' (σ r) l).det‖ < N := by
  intro C _ _ J k P P' N hN hle ⟨σ₀, hσ₀⟩ hclose σ
  classical
  set A : Matrix (Fin k) (Fin k) C := Matrix.of fun r l => P (σ₀ r) l with hA
  have hdetA : A.det ≠ 0 := by
    intro h; rw [h, norm_zero] at hσ₀; linarith
  set Q := A⁻¹ with hQ

  have hcol : ∀ (c : Fin k) (j : J), ‖∑ l, Q l c * P j l‖ ≤ 1 := by
    intro c j
    have h1 : ∑ l, A.adjugate l c * P j l = (A.updateRow c (P j)).det := by
      rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
        ← Matrix.adjugate_transpose]
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
    have h2 : A.updateRow c (P j) = Matrix.of fun r l => P (Function.update σ₀ c j r) l := by
      ext r l
      by_cases hr : r = c
      · subst hr; simp [Matrix.updateRow_apply]
      · simp [Matrix.updateRow_apply, hr, Function.update_of_ne hr, hA]
    have h3 : ∑ l, Q l c * P j l = (A.det)⁻¹ * ∑ l, A.adjugate l c * P j l := by
      rw [hQ, Matrix.inv_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, mul_assoc]
    rw [h3, h1, h2, norm_mul, norm_inv, hσ₀]
    rw [inv_mul_le_iff₀ hN, mul_one]
    exact hle _
  set M : Matrix (Fin k) (Fin k) C := Matrix.of fun r l => P (σ r) l
  set M' : Matrix (Fin k) (Fin k) C := Matrix.of fun r l => P' (σ r) l
  have hB : ∀ r c, ‖(M * Q) r c‖ ≤ 1 := by
    intro r c
    rw [Matrix.mul_apply]
    simpa [M, mul_comm] using hcol c (σ r)
  have hBB : ∀ r c, ‖(M * Q) r c - (M' * Q) r c‖ < 1 := by
    intro r c
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
    have := hclose (fun l => Q l c) (fun j => hcol c j) (σ r)
    convert this using 2
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [M, M']; ring
  have hkey := detClose_norm_det_sub_lt (M * Q) (M' * Q) hB hBB
  have hQA : Q.det * A.det = 1 := by
    rw [hQ, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_mul_cancel₀ hdetA]
  have e : M.det - M'.det = ((M * Q).det - (M' * Q).det) * A.det := by
    rw [Matrix.det_mul, Matrix.det_mul, sub_mul, mul_assoc, mul_assoc, hQA, mul_one, mul_one]
  show ‖M.det - M'.det‖ < N
  rw [e, norm_mul, hσ₀]
  calc ‖(M * Q).det - (M' * Q).det‖ * N < 1 * N := mul_lt_mul_of_pos_right hkey hN
    _ = N := one_mul N

end GlobalTheory
