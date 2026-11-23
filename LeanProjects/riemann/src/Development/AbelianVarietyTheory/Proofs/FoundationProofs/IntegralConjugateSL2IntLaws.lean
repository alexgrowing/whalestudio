import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.CjLaws

end GlobalTheory.KZ.CjLaws

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma mul_eq_cj_mul_of_exists {m : Matrix (Fin 2) (Fin 2) ℤ} {δ : SL(2, ℤ)}
    (h : ∃ δ' : SL(2, ℤ), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
      (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m := by
  unfold _root_.GlobalTheory.KZ.H3.cj
  rw [dif_pos h]
  exact h.choose_spec

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma eq_of_mul_eq_mul_of_det_ne_zero {m δ₁ δ₂ : Matrix (Fin 2) (Fin 2) ℤ} (hm : m.det ≠ 0)
    (h : δ₁ * m = δ₂ * m) : δ₁ = δ₂ := by
  have h2 : δ₁ * m * adjugate m = δ₂ * m * adjugate m := by rw [h]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one] at h2
  exact smul_right_injective _ hm h2

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma mul_eq_cj_mul_and_cj_mem_gamma (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ) (hm : 0 < m.det)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs)) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
      _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M := by
  set d := m.det with hd
  have hd0 : d ≠ 0 := hm.ne'
  have hN : ((M * d.natAbs : ℕ) : ℤ) = (M : ℤ) * d := by
    push_cast
    rw [abs_of_pos hm]
  have hdvd : ∀ i j, ((M : ℤ) * d) ∣
      (δ : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [CongruenceSubgroup.Gamma_mem] at hδ
    obtain ⟨h00, h01, h10, h11⟩ := hδ
    intro i j
    rw [← hN, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    fin_cases i <;> fin_cases j <;> simp_all
  choose X hX using hdvd
  set D : Matrix (Fin 2) (Fin 2) ℤ := 1 + (M : ℤ) • (m * Matrix.of X * adjugate m) with hD
  have hδX : (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + ((M : ℤ) * d) • Matrix.of X := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← hX i j]
    ring
  have hDm : D * m = m * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hD, hδX, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      adjugate_mul, ← Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_add,
      Matrix.mul_one, Matrix.mul_smul, smul_smul]
  have hdetD : D.det = 1 := by
    have h := congrArg Matrix.det hDm
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one] at h
    exact mul_right_cancel₀ hd0 (by rw [h, one_mul])
  have hex : ∃ δ' : SL(2, ℤ),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m :=
    ⟨⟨D, hdetD⟩, hDm.symm⟩
  have h1 := mul_eq_cj_mul_of_exists hex
  refine ⟨h1, ?_⟩
  have h2 : (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) = D :=
    eq_of_mul_eq_mul_of_det_ne_zero hd0 (by rw [← h1, hDm])
  rw [CongruenceSubgroup.Gamma_mem, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    push_cast <;> simp

open Matrix in
open scoped MatrixGroups TensorProduct in
theorem _root_.GlobalTheory.KZ.cj_laws : (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ), 0 < m.det →
    ∀ δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
        _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M) ∧
    (∀ γ δ : SL(2, ℤ), _root_.GlobalTheory.KZ.H3.cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ = γ * δ * γ⁻¹) ∧
    (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (δ δ' : SL(2, ℤ)), 0 < m.det →
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m →
        ∀ z ∈ _root_.GlobalTheory.KZ.Hs,
          _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ) z) =
            _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ')
              (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) z)) := by
  refine ⟨mul_eq_cj_mul_and_cj_mem_gamma, fun γ δ => ?_, fun m δ δ' hm h => ?_⟩
  · have hex : ∃ δ' : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (δ' : Matrix (Fin 2) (Fin 2) ℤ) * γ :=
      ⟨γ * δ * γ⁻¹, by simp [Matrix.mul_assoc, Matrix.adjugate_mul]⟩
    have h1 := mul_eq_cj_mul_of_exists hex
    apply Subtype.ext
    refine eq_of_mul_eq_mul_of_det_ne_zero (m := (γ : Matrix (Fin 2) (Fin 2) ℤ)) (by simp) ?_
    rw [← h1]
    simp [Matrix.mul_assoc, Matrix.adjugate_mul]
  · intro z hz
    obtain ⟨-, hmul, -, -, hcoe, hhom⟩ := _root_.GlobalTheory.KZ.mob_laws
    have hδ : (0 : ℤ) < (δ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    have hδ' : (0 : ℤ) < (δ' : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    rw [← hmul _ _ z hz, ← hmul _ _ z hz, ← hcoe, ← hcoe, ← hhom _ _ hm hδ, ← hhom _ _ hδ' hm, h]
