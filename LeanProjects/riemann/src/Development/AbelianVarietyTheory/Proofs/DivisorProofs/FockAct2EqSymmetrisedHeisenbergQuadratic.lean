import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section
namespace GlobalTheory.FockHeisQuad

variable {P Q R S : ℕ}

theorem heisOp_single (a : Ix P Q) (b : Ix R S) (z : ℂ) :
    heisOp (Matrix.single a b z) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      (z • raiB (a, b) - (lineSign a b * star z) • lowB (a, b)) := by
  unfold heisOp
  congr 1
  rw [Fintype.sum_eq_single (a, b)]
  · simp
  · rintro ⟨a', b'⟩ h
    have : ¬ (a = a' ∧ b = b') := fun ⟨h1, h2⟩ => h (by subst h1; subst h2; rfl)
    simp [Matrix.single_apply, this]

theorem single_mul_tr_apply (a : Ix P Q) (b : Ix R S) (z : ℂ) (Y : Mat R S) (a' : Ix P Q) (b' : Ix R S) :
    (Matrix.single a b z * Yᵀ) a' b' = if a' = a then z * Y b' b else 0 := by
  by_cases h : a' = a
  · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
  · simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm h, h]

theorem heisOp_single_mul (a : Ix P Q) (b : Ix R S) (z : ℂ) (Y : Mat R S) :
    heisOp (Matrix.single a b z * Yᵀ) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      ∑ b' : Ix R S, ((z * Y b' b) • raiB (a, b') - (lineSign a b' * star (z * Y b' b)) • lowB (a, b')) := by
  unfold heisOp
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [single_mul_tr_apply]
  · intro a' _ h
    simp [single_mul_tr_apply, h]
  · simp

end GlobalTheory.FockHeisQuad

noncomputable section
namespace GlobalTheory.FockHeisQuad

theorem quad {A : Type} [Ring A] [Algebra ℂ A] (U V X L : A) (c p ε : ℂ) (hc : c * c = 2 * p) (hp : p ≠ 0)
    (hε : ε = 1 ∨ ε = -1) :
    (4 * p * Complex.I)⁻¹ • ((ε / 4) • (((c • (U - V)) * (c • (Complex.I • (X + ε • L))) +
        (c • (Complex.I • (X + ε • L))) * (c • (U - V))) -
      ((c • (Complex.I • (U + V))) * (c • (X - ε • L)) + (c • (X - ε • L)) * (c • (Complex.I • (U + V)))))) =
      (1 / 4 : ℂ) • ((U * L + L * U) - ε • (V * X + X * V)) := by
  have hp' : p = c * c / 2 := by linear_combination -hc / 2
  subst hp'
  have hc0 : c ≠ 0 := by rintro rfl; simp at hp
  rcases hε with rfl | rfl <;>
  · simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
    match_scalars <;> field_simp <;> ring_nf

variable {R S : ℕ}
theorem upq_entry (Y : Mat R S) (hY : Y ∈ upq R S) {P Q : ℕ} (a : Ix P Q) (b b' : Ix R S) :
    lineSign a b * (lineSign a b' * star (Y b' b)) = - Y b b' := by
  have hJ : Jm R S = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  have h := congrFun (congrFun hY b) b'
  rw [hJ] at h
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [lineSign] at h ⊢ <;> first | linear_combination h | linear_combination -h

end GlobalTheory.FockHeisQuad

noncomputable section
namespace GlobalTheory.FockHeisQuad
variable {P Q R S : ℕ}

theorem fockAct2_expand (Y : Mat R S) :
    fockAct2 P Q R S Y = ∑ a : Ix P Q, ∑ b : Ix R S, ∑ b' : Ix R S, Y b' b • omE (a, b') (a, b) := by
  simp only [fockAct2, LinearMap.comp_apply, omAct_apply,
    Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, LinearMap.mul_apply',
    Fintype.sum_prod_type, Matrix.one_apply]
  simp [ite_smul, Finset.sum_ite_eq, -Fintype.sum_sum_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem lineSign_cases (a : Ix P Q) (b : Ix R S) : lineSign a b = 1 ∨ lineSign a b = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_eq (Y : Mat R S) (hY : Y ∈ upq R S) (a : Ix P Q) (b : Ix R S) :
    (4 * Real.pi * Complex.I : ℂ)⁻¹ • ((lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) =
    ∑ b' : Ix R S, ((1 / 4 : ℂ) * Y b' b) • (raiB (a, b') * lowB (a, b) + lowB (a, b) * raiB (a, b')) +
      ∑ b' : Ix R S, ((1 / 4 : ℂ) * Y b b') • (lowB (a, b') * raiB (a, b) + raiB (a, b) * lowB (a, b')) := by
  set U : Module.End ℂ (Pol P Q R S) := ∑ b' : Ix R S, Y b' b • raiB (a, b') with hU
  set V : Module.End ℂ (Pol P Q R S) := ∑ b' : Ix R S, (lineSign a b' * star (Y b' b)) • lowB (a, b') with hV
  have h1 : heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (U - V) := by
    rw [heisOp_single_mul, hU, hV, ← Finset.sum_sub_distrib]
    simp
  have h2 : heisOp (Matrix.single a b Complex.I * Yᵀ) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (Complex.I • (U + V)) := by
    rw [heisOp_single_mul, hU, hV, ← Finset.sum_add_distrib]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [star_mul', Complex.star_def, Complex.conj_I, smul_add, smul_smul]
    match_scalars <;> ring
  have h3 : heisOp (Matrix.single a b (1 : ℂ)) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (raiB (a, b) - lineSign a b • lowB (a, b)) := by
    rw [heisOp_single]; simp
  have h4 : heisOp (Matrix.single a b Complex.I) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (Complex.I • (raiB (a, b) + lineSign a b • lowB (a, b))) := by
    rw [heisOp_single]
    congr 1
    simp only [Complex.star_def, Complex.conj_I, smul_add, smul_smul]
    match_scalars <;> ring
  have hc : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [h1, h2, h3, h4, quad U V (raiB (a, b)) (lowB (a, b)) _ _ _ hc hπ (lineSign_cases a b)]
  simp only [hU, hV, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← Finset.sum_add_distrib,
    Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have e := upq_entry Y hY a b b'
  clear h1 h2 h3 h4 hc hπ hU hV
  simp only [smul_add, smul_sub, smul_smul]
  match_scalars <;> first | ring1 | linear_combination (-1 / 4 : ℂ) * e

end GlobalTheory.FockHeisQuad

noncomputable section
namespace GlobalTheory.FockHeisQuad

theorem fockAct2_eq_heisOp_quad : ∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ))) := by
  intro P Q R S Y hY
  rw [fockAct2_expand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  simp only [term_eq Y hY a]
  rw [Finset.sum_add_distrib]
  conv_rhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [omE, GlobalTheory.FockCasimir.lowB_mul_raiB (a, b) (a, b')]
  by_cases h : b' = b
  · subst h
    simp only [if_true]
    module
  · have h1 : ((a, b') : Ln P Q R S) ≠ (a, b) := by simp [h]
    simp only [h1, Ne.symm h1, if_false, add_zero]
    module

end GlobalTheory.FockHeisQuad
