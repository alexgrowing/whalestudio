import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix

noncomputable section

open Matrix Formalism.UG GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertSmith

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_zpow_val {ϖ y : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (hy : y ≠ 0) :
    ∃ d : ℤ, Valued.v y = Valued.v (ϖ ^ d) := by
  refine ⟨Formalism.UG.ordL y, ?_⟩
  rw [GlobalTheory.Hk3.Smith.v_eq_ord hy, map_zpow₀, hϖ]
  change _ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ Formalism.UG.ordL y
  rw [← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  simp

theorem isInt_diagonal {n : ℕ} {s : Fin n → L} (hs : ∀ i, Valued.v (s i) = 1) : IsInt (Matrix.diagonal s) := by
  intro i j
  rw [GlobalTheory.Hk3.Smith.mem_intL, Matrix.diagonal_apply]
  split_ifs with h
  · exact (hs i).le
  · simp

theorem smith : Smith := by
  intro L _ _ ϖ n hϖ g hg
  obtain ⟨P, Q, ⟨hPi, P', hP'i, hPP'⟩, ⟨hQi, Q', hQ'i, hQQ'⟩, hD⟩ := GlobalTheory.Hk3.Smith.exists_diag n n g
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  have hdetP : P.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hPP'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hdetQ : Q.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hQQ'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hDdiag : P * g * Q = Matrix.diagonal (fun i => (P * g * Q) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hD i j (fun h => hij (Fin.ext h))
  have hne : ∀ i, (P * g * Q) i i ≠ 0 := by
    have hdet : (P * g * Q).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero hdetP hg) hdetQ
    rw [hDdiag, Matrix.det_diagonal] at hdet
    exact fun i => Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
  have hvϖ : Valued.v ϖ ≠ 0 := by
    rw [hϖ]
    exact WithZero.coe_ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => hvϖ (by rw [h, map_zero])
  choose d hd using fun i => exists_zpow_val hϖ (hne i)
  have hpow0 : ∀ i, ϖ ^ d i ≠ 0 := fun i => zpow_ne_zero _ hϖ0
  obtain ⟨u, hu⟩ : ∃ u : Fin n → L, ∀ i, u i = (P * g * Q) i i / ϖ ^ d i := ⟨_, fun i => rfl⟩
  have hvu : ∀ i, Valued.v (u i) = 1 := by
    intro i
    rw [hu i, map_div₀, hd i, div_self]
    exact fun h => hpow0 i (by
      by_contra h'
      exact h' ((Valuation.zero_iff _).mp h))
  have hvu' : ∀ i, Valued.v ((u i)⁻¹) = 1 := fun i => by rw [map_inv₀, hvu i, inv_one]
  have hu0 : ∀ i, u i ≠ 0 := fun i h => by
    have h1 := hvu i
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hDfac : P * g * Q = Matrix.diagonal (fun i => ϖ ^ d i) * Matrix.diagonal u := by
    rw [Matrix.diagonal_mul_diagonal]
    conv_lhs => rw [hDdiag]
    congr 1
    funext i
    rw [hu i]
    field_simp
  have hinv : (fun i => u i * (u i)⁻¹) = fun _ => (1 : L) := funext fun i => mul_inv_cancel₀ (hu0 i)
  refine ⟨d, P', P, Matrix.diagonal u * Q', Q * Matrix.diagonal (fun i => (u i)⁻¹), hP'i, hPi,
    GlobalTheory.Hk3.Smith.mul_int (isInt_diagonal hvu) hQ'i, GlobalTheory.Hk3.Smith.mul_int hQi (isInt_diagonal hvu'),
    hPP', ?_, ?_⟩
  · calc Matrix.diagonal u * Q' * (Q * Matrix.diagonal fun i => (u i)⁻¹)
        = Matrix.diagonal u * (Q' * Q) * Matrix.diagonal (fun i => (u i)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [mul_eq_one_comm.mp hQQ', Matrix.mul_one, Matrix.diagonal_mul_diagonal, hinv,
            Matrix.diagonal_one]
  · calc g = P' * (P * g * Q) * Q' := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'P, Matrix.one_mul, Matrix.mul_assoc, hQQ',
            Matrix.mul_one]
      _ = _ := by
          rw [hDfac]
          simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.InertSmith

end
