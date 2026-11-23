import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermitianSqrtInSignedUnitaryGroupStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ Jm_mul_self Jm_conjTranspose)

noncomputable section

namespace GlobalTheory.FrameCompletion

theorem resolution {n n₀ : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (hn : n = n₀ + 2 * Fintype.card κ)
    (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin n₀) (Fin n₀) ℂ) (hJ : Jᴴ = J) (hJJ : J * J = 1)
    (hJ₀ : J₀ * J₀ = 1) (P : Matrix (Fin n) κ ℂ) (C : Matrix (Fin n) (Fin n₀) ℂ)
    (h1 : Pᴴ * P = 1) (h2 : Pᴴ * J * P = 0) (h3 : Pᴴ * C = 0) (h4 : Pᴴ * J * C = 0) (h5 : Cᴴ * J * C = J₀) :
    P * Pᴴ + J * (P * Pᴴ) * J + C * J₀ * Cᴴ * J = 1 := by

  have a2 : Pᴴ * (J * P) = 0 := by rw [← Matrix.mul_assoc]; exact h2
  have a4 : Pᴴ * (J * (J * P)) = 1 := by rw [← Matrix.mul_assoc J, hJJ, Matrix.one_mul, h1]
  have a6 : Pᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc]; exact h4
  have hCP : Cᴴ * P = 0 := by
    have := congrArg conjTranspose h3
    simpa [conjTranspose_mul] using this
  have hCJP : Cᴴ * (J * P) = 0 := by
    have := congrArg conjTranspose h4
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have a7 : J₀ * (Cᴴ * (J * P)) = 0 := by rw [hCJP, Matrix.mul_zero]
  have a8 : J₀ * (Cᴴ * (J * (J * P))) = 0 := by
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul, hCP, Matrix.mul_zero]
  have a9 : J₀ * (Cᴴ * (J * C)) = 1 := by rw [← Matrix.mul_assoc Cᴴ, h5, hJ₀]
  have hLM : fromRows (fromRows Pᴴ (Pᴴ * J)) (J₀ * Cᴴ * J) * fromCols (fromCols P (J * P)) C = 1 := by
    rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [h1, a2, a4, h3, a6, a7, a8, a9, fromRows_zero, fromCols_zero, fromBlocks_one, fromBlocks_one]
  have hcard : Fintype.card ((κ ⊕ κ) ⊕ Fin n₀) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin, hn]
    ring
  have hML := (mul_eq_one_comm_of_card_eq ((κ ⊕ κ) ⊕ Fin n₀) (Fin n) ℂ hcard).mp hLM
  rw [← hML]
  simp only [fromCols_mul_fromRows, Matrix.mul_assoc]

theorem exists_square {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℂ) :
    ∃ D : Matrix (Fin m) (Fin m) ℂ, Dᴴ * D = Cᴴ * C := by
  open ComplexOrder MatrixOrder in
  have h0 : (0 : Matrix (Fin m) (Fin m) ℂ) ≤ Cᴴ * C := (posSemidef_conjTranspose_mul_self C).nonneg
  open ComplexOrder MatrixOrder in
  refine ⟨CFC.sqrt (Cᴴ * C), ?_⟩
  open ComplexOrder MatrixOrder in
  rw [← star_eq_conjTranspose, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (Cᴴ * C))).star_eq]
  open ComplexOrder MatrixOrder in
  exact CFC.sqrt_mul_sqrt_self (Cᴴ * C) h0

theorem exists_isFrame : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ), n = n₀ + 2 * ∑ i, j i → (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → (∀ i k, (B i)ᴴ * Formalism.REAL.Jm ε * B k = 0) → (∀ i, (B i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → ∃ (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (s : Formalism.REAL.UJ ε₀) (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ ∧ A₀ = B₀ * uMat s + ∑ k, B k * d k := by
  intro n n₀ a j ε ε₀ B A₀ hn h1 h2 h3 h4 h5
  classical
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  have hJ₀J₀ : Jm ε₀ * Jm ε₀ = 1 := Jm_mul_self ε₀
  have hJ₀h : (Jm ε₀)ᴴ = Jm ε₀ := Jm_conjTranspose ε₀
  have hJJX : ∀ {m : Type} [Fintype m] (X : Matrix (Fin n) m ℂ), Jm ε * (Jm ε * X) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]

  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Σ i, Fin (j i)) ℂ, P = Matrix.of fun r x => B x.1 r x.2 := ⟨_, rfl⟩
  have hPe : ∀ {m : Type} [Fintype m] (X : Matrix (Fin n) m ℂ) (x : Σ i, Fin (j i)) (d : m),
      (Pᴴ * X) x d = ((B x.1)ᴴ * X) x.2 d := by
    intro m _ X x d
    simp [hP, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hPc : ∀ {m : Type} [Fintype m] (X : Matrix m (Fin n) ℂ) (c : m) (x : Σ i, Fin (j i)),
      (X * P) c x = (X * B x.1) c x.2 := by
    intro m _ X c x
    simp [hP, Matrix.mul_apply]
  have hPPX : ∀ {m : Type} [Fintype m] (X : Matrix (Fin n) m ℂ),
      P * (Pᴴ * X) = ∑ i, B i * ((B i)ᴴ * X) := by
    intro m _ X
    ext r d
    simp only [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_sigma, hP, Matrix.of_apply,
      Matrix.conjTranspose_apply]
  have hPP : Pᴴ * P = 1 := by
    ext ⟨i, c⟩ ⟨k, d⟩
    rw [hPc, hPe]
    by_cases hik : i = k
    · subst hik
      simp [h1, Matrix.one_apply]
    · simp [h2 i k hik, hik]
  have hPJP : Pᴴ * Jm ε * P = 0 := by
    ext ⟨i, c⟩ ⟨k, d⟩
    rw [hPc, Matrix.mul_assoc, hPe, ← Matrix.mul_assoc]
    simp [h3 i k]
  have hPJA : Pᴴ * (Jm ε * A₀) = 0 := by
    ext ⟨i, c⟩ d
    rw [hPe, ← Matrix.mul_assoc]
    simp [h4 i]

  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin n) (Fin n₀) ℂ, C = A₀ - P * (Pᴴ * A₀) := ⟨_, rfl⟩
  have hPC : Pᴴ * C = 0 := by
    rw [hC, Matrix.mul_sub, ← Matrix.mul_assoc Pᴴ P, hPP, Matrix.one_mul, sub_self]
  have hJC0 : Jm ε * C = Jm ε * A₀ - Jm ε * P * (Pᴴ * A₀) := by
    rw [hC, Matrix.mul_sub, Matrix.mul_assoc]
  have hPJC : Pᴴ * (Jm ε * C) = 0 := by
    have hPJP' : Pᴴ * (Jm ε * P) = 0 := by rw [← Matrix.mul_assoc]; exact hPJP
    rw [hJC0, Matrix.mul_sub, hPJA, ← Matrix.mul_assoc Pᴴ, hPJP', Matrix.zero_mul, sub_zero]
  have hCJP : Cᴴ * (Jm ε * P) = 0 := by
    have := congrArg conjTranspose hPJC
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hAJP : A₀ᴴ * (Jm ε * P) = 0 := by
    have := congrArg conjTranspose hPJA
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hCJC : Cᴴ * (Jm ε * C) = Jm ε₀ := by
    rw [hJC0, Matrix.mul_sub, ← Matrix.mul_assoc Cᴴ (Jm ε * P), hCJP, Matrix.zero_mul, sub_zero, hC,
      conjTranspose_sub, Matrix.sub_mul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc, Matrix.mul_assoc, hPJA, Matrix.mul_zero, Matrix.mul_zero, sub_zero,
      ← Matrix.mul_assoc, h5]
  have hcard : n = n₀ + 2 * Fintype.card (Σ i, Fin (j i)) := by
    simp [Fintype.card_sigma, hn]
  have hres := resolution hcard (Jm ε) (Jm ε₀) hJh hJJ hJ₀J₀ P C hPP hPJP hPC
    (by rw [Matrix.mul_assoc]; exact hPJC) (by rw [Matrix.mul_assoc]; exact hCJC)

  have hJC : Jm ε * C = C * (Jm ε₀ * (Cᴴ * C)) := by
    calc Jm ε * C
        = (P * Pᴴ + Jm ε * (P * Pᴴ) * Jm ε + C * Jm ε₀ * Cᴴ * Jm ε) * (Jm ε * C) := by
          rw [hres, Matrix.one_mul]
      _ = P * (Pᴴ * (Jm ε * C)) + Jm ε * (P * (Pᴴ * (Jm ε * (Jm ε * C))))
          + C * (Jm ε₀ * (Cᴴ * (Jm ε * (Jm ε * C)))) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = C * (Jm ε₀ * (Cᴴ * C)) := by
          rw [hPJC, hJJX, hPC]
          simp
  have hCJ : Cᴴ * Jm ε = Cᴴ * (C * (Jm ε₀ * Cᴴ)) := by
    have := congrArg conjTranspose hJC
    simpa [conjTranspose_mul, hJh, hJ₀h, Matrix.mul_assoc] using this
  have hHJH : (Cᴴ * C) * Jm ε₀ * (Cᴴ * C) = Jm ε₀ := by
    calc (Cᴴ * C) * Jm ε₀ * (Cᴴ * C) = Cᴴ * (C * (Jm ε₀ * (Cᴴ * C))) := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * (Jm ε * C) := by rw [hJC]
      _ = Jm ε₀ := hCJC
  obtain ⟨D, hD⟩ := exists_square C
  have hdetJ₀ : (Jm ε₀).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hJ₀J₀
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet : D.det ≠ 0 := by
    intro h0
    have hH : (Cᴴ * C).det = 0 := by rw [← hD, Matrix.det_mul, h0, mul_zero]
    have := congrArg Matrix.det hHJH
    rw [Matrix.det_mul, Matrix.det_mul, hH, zero_mul, zero_mul] at this
    exact hdetJ₀ this.symm
  obtain ⟨s, hsh, hss⟩ := GlobalTheory.T.exists_hermitian_sqrt_in_signedUnitaryGroup n₀ ε₀ D hdet (by rw [hD]; exact hHJH)
  rw [hD] at hss
  obtain ⟨S, hS⟩ : ∃ S, S = uMat s := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Matrix (Fin n₀) (Fin n₀) ℂ,
      S' = (((s : (Matrix (Fin n₀) (Fin n₀) ℂ)ˣ)⁻¹ : (Matrix (Fin n₀) (Fin n₀) ℂ)ˣ) : Matrix (Fin n₀) (Fin n₀) ℂ) :=
    ⟨_, rfl⟩
  have hSS' : S * S' = 1 := by rw [hS, hS']; exact Units.mul_inv _
  have hS'S : S' * S = 1 := by rw [hS, hS']; exact Units.inv_mul _
  rw [← hS] at hsh hss
  have hsJ : Sᴴ * Jm ε₀ * S = Jm ε₀ := by rw [hS]; exact s.2
  rw [hsh] at hsJ
  have hSS'h : S * S'ᴴ = 1 := by
    have := congrArg conjTranspose hS'S
    simpa [conjTranspose_mul, hsh] using this
  have hS'h : S'ᴴ = S' := by
    calc S'ᴴ = S' * S * S'ᴴ := by rw [hS'S, Matrix.one_mul]
      _ = S' := by rw [Matrix.mul_assoc, hSS'h, Matrix.mul_one]
  have hJ₀S : Jm ε₀ * S = S' * Jm ε₀ := by
    calc Jm ε₀ * S = S' * S * Jm ε₀ * S := by rw [hS'S, Matrix.one_mul]
      _ = S' * (S * Jm ε₀ * S) := by simp only [Matrix.mul_assoc]
      _ = S' * Jm ε₀ := by rw [hsJ]
  have hBC : ∀ i, (B i)ᴴ * C = 0 := by
    intro i
    ext c d
    have := congrFun (congrFun hPC ⟨i, c⟩) d
    rw [hPe] at this
    simpa using this
  refine ⟨C * S', s, fun k => (B k)ᴴ * A₀, ?_, ?_⟩
  · refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [← Matrix.mul_assoc, hBC i, Matrix.zero_mul]
    · calc (C * S')ᴴ * (C * S') = S'ᴴ * ((Cᴴ * C) * S') := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by
            rw [hS'h, ← hss, Matrix.mul_assoc, hSS', Matrix.mul_one, hS'S]
    · calc Jm ε * (C * S') = C * (Jm ε₀ * (Cᴴ * C)) * S' := by
            rw [← Matrix.mul_assoc, hJC]
        _ = C * (Jm ε₀ * S) * (S * S') := by
            rw [← hss]; simp only [Matrix.mul_assoc]
        _ = C * S' * Jm ε₀ := by
            rw [hSS', Matrix.mul_one, hJ₀S, Matrix.mul_assoc]
    · have hsum : ∑ i, B i * (B i)ᴴ = P * Pᴴ := by
        have := hPPX (1 : Matrix (Fin n) (Fin n) ℂ)
        simpa using this.symm
      have hsumJ : ∑ i, Jm ε * B i * (B i)ᴴ * Jm ε = Jm ε * (P * Pᴴ) * Jm ε := by
        rw [← hsum, Finset.mul_sum, Finset.sum_mul]
        simp only [Matrix.mul_assoc]
      have hlast : C * S' * (C * S')ᴴ = C * Jm ε₀ * Cᴴ * Jm ε := by
        calc C * S' * (C * S')ᴴ = C * (S' * S') * Cᴴ := by
              simp only [conjTranspose_mul, hS'h, Matrix.mul_assoc]
          _ = C * (Jm ε₀ * (S * (S * Jm ε₀))) * Cᴴ := by
              congr 2
              symm
              rw [← Matrix.mul_assoc (Jm ε₀) S, hJ₀S, Matrix.mul_assoc S', ← Matrix.mul_assoc (Jm ε₀) S, hJ₀S,
                Matrix.mul_assoc S', hJ₀J₀, Matrix.mul_one]
          _ = C * Jm ε₀ * Cᴴ * Jm ε := by
              rw [Matrix.mul_assoc (C * Jm ε₀), hCJ, ← Matrix.mul_assoc Cᴴ C, ← hss]
              simp only [Matrix.mul_assoc]
      rw [hsum, hsumJ, hlast]
      exact hres
  · have hsum : ∑ k, B k * ((B k)ᴴ * A₀) = P * (Pᴴ * A₀) := (hPPX A₀).symm
    simp only [hsum, Matrix.mul_assoc]
    rw [← hS, hS'S, Matrix.mul_one, hC, sub_add_cancel]

end GlobalTheory.FrameCompletion
