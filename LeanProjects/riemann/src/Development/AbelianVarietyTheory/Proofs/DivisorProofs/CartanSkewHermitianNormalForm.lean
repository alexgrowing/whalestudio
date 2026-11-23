import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.CartanFrame

open Matrix
open scoped ComplexOrder

theorem exists_conjTranspose_mul_self_of_psd {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.PosSemidef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, T = Bᴴ * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

theorem herm_invol_diag {n : ℕ} {S : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsHermitian) (h2 : S * S = 1) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Uᴴ * U = 1 ∧
      S * U = U * diagonal (fun j => (d j : ℂ)) ∧ ∀ j, d j = 1 ∨ d j = -1 := by
  have hU : (hS.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ * hS.eigenvectorUnitary = 1 :=
    Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hSU : S * (hS.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      (hS.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun j => (hS.eigenvalues j : ℂ)) := by
    ext i j
    rw [mul_diagonal]
    have := congrFun (congrArg (fun v => (v : Fin n → ℂ)) (hS.mulVec_eigenvectorBasis j)) i
    simp only [Pi.smul_apply, Complex.real_smul] at this
    rw [Matrix.IsHermitian.eigenvectorUnitary_apply, mul_comm]
    exact this
  refine ⟨_, hS.eigenvalues, hU, hSU, fun j => ?_⟩
  have hDD : diagonal (fun j => (hS.eigenvalues j : ℂ)) * diagonal (fun j => (hS.eigenvalues j : ℂ)) = 1 := by
    have e : (hS.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ * (S * S) * hS.eigenvectorUnitary =
        diagonal (fun j => (hS.eigenvalues j : ℂ)) * diagonal (fun j => (hS.eigenvalues j : ℂ)) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hSU, ← Matrix.mul_assoc S, hSU, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [← e, h2, Matrix.mul_one, hU]
  have := congrFun (congrFun hDD j) j
  rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at this
  have h' : hS.eigenvalues j * hS.eigenvalues j = 1 := by exact_mod_cast this
  exact mul_self_eq_one_iff.mp h'

end GlobalTheory.CartanFrame

namespace GlobalTheory.CartanFrame
open Matrix
open scoped ComplexOrder

theorem frame (n : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (hz : star z = -z) (hz0 : z ≠ 0)
    (hM : ∀ i j, star (M j i) = -M i j) (hC : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • M) θ) :
    ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧
      Pᴴ * (z • M.map star) * P = Formalism.REAL.Jm ε ∧ ∃ c : ℂ, c ≠ 0 ∧ P * Formalism.REAL.Jm ε = c • (θ * P) := by
  obtain ⟨h1, h2, h3⟩ := hC
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) ℂ, N = Complex.I • M := ⟨_, rfl⟩
  rw [← hN] at h2 h3
  have hNe : ∀ i j, N i j = Complex.I * M i j := fun i j => by rw [hN]; rfl
  have hNs : N.map star = Nᵀ := by
    ext i j
    rw [map_apply, transpose_apply, hNe, hNe, star_mul', hM j i]
    simp [Complex.star_def, Complex.conj_I]
  have hT : (Nᵀ)ᴴ = Nᵀ := by
    rw [conjTranspose, transpose_transpose, hNs]
  have hθc : θᴴ = (θ.map star)ᵀ := by ext i j; rfl
  have h2' : θᴴ * Nᵀ * θ = Nᵀ := by
    have := congrArg transpose h2
    rw [transpose_mul, transpose_mul, transpose_transpose] at this
    rw [hθc, Matrix.mul_assoc, this]
  have hMs : z • M.map star = (z * Complex.I) • Nᵀ := by
    ext i j
    rw [Matrix.smul_apply, Matrix.smul_apply, map_apply, transpose_apply, hNe, hM]
    simp only [smul_eq_mul]
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-(z * M j i)) * this

  have hAh : (Nᵀ * θ)ᴴ = Nᵀ * θ := by
    rw [conjTranspose_mul, hT]
    calc θᴴ * Nᵀ = θᴴ * Nᵀ * θ * θ := by rw [Matrix.mul_assoc _ θ θ, h1, Matrix.mul_one]
      _ = Nᵀ * θ := by rw [h2']
  have hAθ : Nᵀ * θ * θ = Nᵀ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hform : ∀ x : Fin n → ℂ, star x ⬝ᵥ ((Nᵀ * θ) *ᵥ x) = (θ *ᵥ x) ⬝ᵥ N *ᵥ star x := by
    intro x
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hPD : (Nᵀ * θ).PosDef := by
    refine posDef_iff_dotProduct_mulVec.2 ⟨hAh, fun x hx => Complex.pos_iff.2 ⟨?_, ?_⟩⟩
    · rw [hform]; exact h3 x hx
    · exact ((show (Nᵀ * θ).IsHermitian from hAh).im_star_dotProduct_mulVec_self x).symm
  obtain ⟨B, hB⟩ := exists_conjTranspose_mul_self_of_psd hPD.posSemidef
  have hdA : (Nᵀ * θ).det ≠ 0 := hPD.det_pos.ne'
  have hdB : B.det ≠ 0 := by
    intro h; apply hdA; rw [hB, det_mul, h, mul_zero]
  have hBC : B * B⁻¹ = 1 := mul_nonsing_inv B (isUnit_iff_ne_zero.2 hdB)
  have hCB : B⁻¹ * B = 1 := nonsing_inv_mul B (isUnit_iff_ne_zero.2 hdB)
  obtain ⟨C, hC⟩ : ∃ C, C = B⁻¹ := ⟨_, rfl⟩
  rw [← hC] at hBC hCB
  have hNB : Nᵀ = Bᴴ * B * θ := by rw [← hB, hAθ]
  have hSe : Cᴴ * Nᵀ * C = B * θ * C := by
    rw [hNB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, hBC, conjTranspose_one, Matrix.one_mul]
  have hSh : (Cᴴ * Nᵀ * C).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, hT, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hSS : (Cᴴ * Nᵀ * C) * (Cᴴ * Nᵀ * C) = 1 := by
    rw [hSe]
    calc B * θ * C * (B * θ * C) = B * θ * (C * B) * θ * C := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCB, Matrix.mul_one, Matrix.mul_assoc B θ θ, h1, Matrix.mul_one, hBC]
  obtain ⟨U, d, hU, hSU, hd⟩ := herm_invol_diag hSh hSS
  have hCS : C * (Cᴴ * Nᵀ * C) = θ * C := by
    rw [hSe]; simp only [← Matrix.mul_assoc, hCB, Matrix.one_mul]
  have hθQ : θ * (C * U) = C * U * diagonal (fun j => (d j : ℂ)) := by
    rw [← Matrix.mul_assoc, ← hCS, Matrix.mul_assoc, hSU, Matrix.mul_assoc]
  have hQ : (C * U)ᴴ * Nᵀ * (C * U) = diagonal (fun j => (d j : ℂ)) := by
    calc (C * U)ᴴ * Nᵀ * (C * U) = Uᴴ * ((Cᴴ * Nᵀ * C) * U) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hSU, ← Matrix.mul_assoc, hU, Matrix.one_mul]

  have hw : star (z * Complex.I) = z * Complex.I := by
    rw [star_mul', hz, Complex.star_def, Complex.conj_I]; ring
  have hwr : ((z * Complex.I).re : ℂ) = z * Complex.I := Complex.conj_eq_iff_re.mp hw
  have hwre : (z * Complex.I).re ≠ 0 := by
    intro h; rw [h, Complex.ofReal_zero] at hwr
    exact hz0 (by simpa [Complex.I_ne_zero] using hwr.symm)
  set a := (z * Complex.I).re with ha
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Real.sqrt |a|)⁻¹ := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = a / |a| := ⟨_, rfl⟩
  have hr0 : r ≠ 0 := by
    rw [hr]; exact inv_ne_zero (Real.sqrt_ne_zero'.2 (abs_pos.2 hwre))
  have hrr : r * a * r = σ := by
    rw [hσ, hr, mul_comm, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt (abs_nonneg a), div_eq_inv_mul]
  have hσ1 : σ = 1 ∨ σ = -1 := by
    rw [hσ]
    rcases lt_or_gt_of_ne hwre with h | h
    · right; rw [abs_of_neg h, div_neg, div_self hwre]
    · left; rw [abs_of_pos h, div_self hwre]
  have hσ0 : (σ : ℂ) ≠ 0 := by
    rcases hσ1 with h | h <;> simp [h]
  let ε : Fin n → Bool := fun j => decide (σ * d j = 1)
  have hJ : Formalism.REAL.Jm ε = (σ : ℂ) • diagonal (fun j => (d j : ℂ)) := by
    rw [Formalism.REAL.Jm, ← diagonal_smul]
    congr 1
    funext j
    simp only [ε, Pi.smul_apply, smul_eq_mul]
    have hsd : σ * d j = 1 ∨ σ * d j = -1 := by
      rcases hσ1 with h | h <;> rcases hd j with h' | h' <;> simp [h, h']
    by_cases h : σ * d j = 1
    · simp only [h, decide_true, if_true]
      exact_mod_cast h.symm
    · have h' : σ * d j = -1 := hsd.resolve_left h
      simp only [h, decide_false, Bool.false_eq_true, if_false]
      exact_mod_cast h'.symm
  refine ⟨ε, (r : ℂ) • (C * U), ?_, ?_, σ, hσ0, ?_⟩
  · rw [isUnit_iff_isUnit_det, det_smul, det_mul, isUnit_iff_ne_zero]
    have hdC : C.det ≠ 0 := by
      intro h; have := congrArg det hBC; rw [det_mul, h, mul_zero, det_one] at this; exact zero_ne_one this
    have hdU : U.det ≠ 0 := by
      intro h; have := congrArg det hU; rw [det_mul, h, mul_zero, det_one] at this; exact zero_ne_one this
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hr0)) (mul_ne_zero hdC hdU)
  · rw [hMs, ← hwr, hJ, conjTranspose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hQ]
    congr 1
    rw [← hrr]; simp [Complex.star_def]; ring
  · rw [hJ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hθQ]

end GlobalTheory.CartanFrame
