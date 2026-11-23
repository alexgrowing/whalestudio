import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.MulVarSpan

variable {P Q R S : ℕ}

theorem heisOp_single (l : Ln P Q R S) (a : ℂ) :
    heisOp (Matrix.single l.1 l.2 a) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      (a • raiB l - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star a) • lowB l) := by
  unfold heisOp
  congr 1
  rw [Finset.sum_eq_single l]
  · simp [Matrix.single_apply]
  · intro l' _ hne
    have h : ¬ (l.1 = l'.1 ∧ l.2 = l'.2) := by
      rintro ⟨h1, h2⟩; exact hne (Prod.ext h1.symm h2.symm)
    simp [Matrix.single_apply, h]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem sq_ne (l : Ln P Q R S) : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast this.ne'

theorem lineSign_sq (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  cases a <;> cases b <;> simp [lineSign]

theorem raiB_mem (l : Ln P Q R S) :
    raiB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  have key : (2 * s) • raiB l = heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    generalize lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 = σ
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (2 * s) ≠ 0 := mul_ne_zero two_ne_zero (sq_ne l)
  have : raiB l = (2 * s)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (sub_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

theorem lowB_mem (l : Ln P Q R S) :
    lowB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  set σ := lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 with hσ
  have hσσ : σ * σ = 1 := lineSign_sq l.1 l.2
  have key : (-2 * s * σ) • lowB l = heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single, ← hσ]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (-2 * s * σ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) (sq_ne l)) ?_
    intro h; rw [h, zero_mul] at hσσ; exact zero_ne_one hσσ
  have : lowB l = (-2 * s * σ)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (add_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

theorem mulX_mem_span : ∀ {P Q R S : ℕ} (l : Ln P Q R S), LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈
    Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  intro P Q R S l
  cases h : linePos l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = lowB l := by simp [lowB, h]
    rw [e]; exact lowB_mem l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = raiB l := by simp [raiB, h]
    rw [e]; exact raiB_mem l

end GlobalTheory.MulVarSpan
