import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.UJOffDiag

open Formalism.REAL

def sgn (e : Bool) : ℝ := if e then 1 else -1

def ind (e : Bool) : ℝ := if e then 1 else 0

lemma term_left (z : ℂ) (e : Bool) :
    star z * (if e then (1 : ℂ) else -1) * z = ((sgn e * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  cases e
  · rw [show star z * (if false = true then (1 : ℂ) else -1) * z = -(star z * z) by simp, h]
    simp [sgn]
  · rw [show star z * (if true = true then (1 : ℂ) else -1) * z = star z * z by simp, h]
    simp [sgn]

lemma term_right (z : ℂ) (e : Bool) :
    z * (if e then (1 : ℂ) else -1) * star z = ((sgn e * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [show z * (if e then (1 : ℂ) else -1) * star z = star z * (if e then (1 : ℂ) else -1) * z by ring]
  exact term_left z e

lemma col_id {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) (b : Fin n) :
    ∑ a, sgn (ε a) * ‖g a b‖ ^ 2 = sgn (ε b) := by
  unfold inUJ at hg
  have h := congrFun (congrFun hg b) b
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply] at h
  simp only [term_left] at h
  have h2 : ((∑ a, sgn (ε a) * ‖g a b‖ ^ 2 : ℝ) : ℂ) = ((sgn (ε b) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h, Matrix.diagonal_apply_eq]; cases ε b <;> simp [sgn]
  exact_mod_cast h2

lemma row_id {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) (a : Fin n) :
    ∑ b, sgn (ε b) * ‖g a b‖ ^ 2 = sgn (ε a) := by
  have h1 := (indefinite_unitary_inv_closed n ε g hg).1
  have hJ : g * Jm ε * gᴴ = Jm ε := by
    calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
          simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
      _ = Jm ε := by rw [h1, Matrix.one_mul]
  have h := congrFun (congrFun hJ a) a
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply] at h
  simp only [term_right] at h
  have h2 : ((∑ b, sgn (ε b) * ‖g a b‖ ^ 2 : ℝ) : ℂ) = ((sgn (ε a) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h, Matrix.diagonal_apply_eq]; cases ε a <;> simp [sgn]
  exact_mod_cast h2

end GlobalTheory.UJOffDiag

namespace GlobalTheory.UJOffDiag

open Formalism.REAL

lemma off_sum_eq {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 =
      ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖M a b‖ ^ 2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun z : Fin n × Fin n => ε z.1 = true ∧ ε z.2 = false)
    (fun x => by simp) (fun z => ‖M z.1 z.2‖ ^ 2), Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  cases ε a <;> cases ε b <;> simp [ind]

lemma hs_eq {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    hs g = n + 4 * ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2 := by
  have key : ∀ a b, ‖g a b‖ ^ 2 = 4 * (ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
      (-(sgn (ε a) * ‖g a b‖ ^ 2) + 2 * (ind (ε a) * (sgn (ε b) * ‖g a b‖ ^ 2))) := by
    intro a b; cases ε a <;> cases ε b <;> simp [ind, sgn] <;> ring
  have hcol : ∑ a, ∑ b, sgn (ε a) * ‖g a b‖ ^ 2 = ∑ b, sgn (ε b) := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _ => col_id ε g hg b
  have hrow : ∑ a, ind (ε a) * ∑ b, sgn (ε b) * ‖g a b‖ ^ 2 = ∑ a, ind (ε a) * sgn (ε a) :=
    Finset.sum_congr rfl fun a _ => by rw [row_id ε g hg a]
  have hn : ∑ a : Fin n, (-(sgn (ε a)) + 2 * (ind (ε a) * sgn (ε a))) = n := by
    rw [show (n : ℝ) = ∑ _a : Fin n, (1 : ℝ) by simp]
    exact Finset.sum_congr rfl fun a _ => by cases ε a <;> simp [ind, sgn] <;> norm_num
  calc hs g = ∑ a, ∑ b, (4 * (ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
      (-(sgn (ε a) * ‖g a b‖ ^ 2) + 2 * (ind (ε a) * (sgn (ε b) * ‖g a b‖ ^ 2)))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b
    _ = 4 * (∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
        (-(∑ a, ∑ b, sgn (ε a) * ‖g a b‖ ^ 2) +
          2 * ∑ a, ind (ε a) * ∑ b, sgn (ε b) * ‖g a b‖ ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_neg_distrib]
    _ = n + 4 * ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2 := by
        rw [hcol, hrow, ← hn, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
        ring

end GlobalTheory.UJOffDiag

namespace GlobalTheory

open Formalism.REAL

theorem isCompact_offDiag_sublevel : ∀ (n : ℕ) (ε : Fin n → Bool) (C : ℝ),
    IsCompact {g : UJ ε | ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false},
      ‖(toM g) z.1.1 z.1.2‖ ^ 2 ≤ C} := by
  intro n ε C
  set F : Matrix (Fin n) (Fin n) ℂ → ℝ := fun M =>
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 with hF
  have hFc : Continuous F :=
    continuous_finset_sum _ fun z _ => (continuous_norm.comp (continuous_id.matrix_elem z.1.1 z.1.2)).pow 2
  have hK : IsCompact {M : Matrix (Fin n) (Fin n) ℂ | inUJ ε M ∧ F M ≤ C} := by
    refine IsCompact.of_isClosed_subset ((hermitian_small_ball n ε).1 (n + 4 * C)) ?_ ?_
    · exact (indefinite_unitary_closed n ε).inter (isClosed_le hFc continuous_const)
    · rintro M ⟨hM, hFM⟩
      refine ⟨hM, ?_⟩
      rw [UJOffDiag.hs_eq ε M hM, ← UJOffDiag.off_sum_eq]
      have : F M = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 := rfl
      linarith
  have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage hK
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

end GlobalTheory
