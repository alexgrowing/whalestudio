import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameExists

theorem exists_signFrame {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (hd : IsUnit H.det) :
    ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = H := by
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  let l := hH.eigenvalues
  let S : Matrix (Fin n) (Fin n) ℂ := diagonal fun a => ((Real.sqrt |l a| : ℝ) : ℂ)
  have hs : H = U * diagonal (fun a => ((l a : ℝ) : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hS : Sᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * S = diagonal (fun a => ((l a : ℝ) : ℂ)) := by
    simp only [S, Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext a
    have h1 : ((Real.sqrt |l a| : ℝ) : ℂ) * ((Real.sqrt |l a| : ℝ) : ℂ) = ((|l a| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [mul_right_comm, h1]
    by_cases h : 0 < l a
    · simp [h, abs_of_pos h]
    · simp [h, abs_of_nonpos (not_lt.1 h)]
  have key : (S * Uᴴ)ᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * (S * Uᴴ) = H := by
    rw [hs, ← hS, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  refine ⟨_, S * Uᴴ, ?_, key⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [← key, det_mul] at hd
  exact isUnit_of_mul_isUnit_right hd

theorem exists_perm_of_card {n : ℕ} {ε η : Fin n → Bool}
    (h : Nat.card {a // ε a = true} = Nat.card {a // η a = true}) :
    ∃ σ : Fin n ≃ Fin n, ∀ a, ε (σ a) = η a := by
  have hf : ∀ b : Bool, Nonempty ({a // η a = b} ≃ {a // ε a = b}) := by
    intro b
    rw [← Finite.card_eq]
    cases b
    · have e : ∀ θ : Fin n → Bool, Nat.card {a // θ a = false} = n - Nat.card {a // θ a = true} := by
        intro θ
        have := Fintype.card_subtype_compl (fun a => θ a = true)
        simp only [Nat.card_eq_fintype_card]
        simpa using this
      rw [e, e, h]
    · exact h.symm
  exact ⟨Equiv.ofFiberEquiv fun b => (hf b).some, fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem exists_signCompat {n p q : ℕ} {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature (Pᴴ * Formalism.REAL.Jm ε * P) p q) :
    ∃ e : Fin p ⊕ Fin q ≃ Fin n, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e := by
  obtain ⟨e, Q, hQ⟩ := h
  have hc : Formalism.UG.cT (starRingEnd ℂ) (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
      (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := rfl
  rw [hc] at hQ
  have h1 : (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e)ᴴ * Formalism.REAL.Jm ε *
      (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e) =
      Formalism.REAL.Jm fun a => (e a).isLeft := by
    have h2 := congrArg (fun M => Matrix.submatrix M e e) hQ
    simp only [← submatrix_mul_equiv _ _ _ e, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self,
      submatrix_id_id] at h2
    rw [conjTranspose_mul, conjTranspose_submatrix]
    simp only [Matrix.mul_assoc] at h2 ⊢
    rw [h2]
    ext a b
    obtain ⟨x, rfl⟩ := e.symm.surjective a
    obtain ⟨y, rfl⟩ := e.symm.surjective b
    simp only [submatrix_apply, Formalism.REAL.Jm, Formalism.UG.Jpq, diagonal_apply, Equiv.apply_symm_apply]
    rcases x with i | i <;> rcases y with j | j <;> simp [Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨σ, hσ⟩ := exists_perm_of_card (GlobalTheory.SignCount.card_true_eq _ h1)
  exact ⟨e.symm.trans σ, fun a => by simp [hσ]⟩

theorem frame_exists_signCompat : ∀ (D : D7) (V : HSp D), Nonempty (GlobalTheory.ChainFr.Fr V) ∧ ∀ (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) (p q : ℕ), Formalism.UG.HasSignature (gramAt D V τ) p q → ∃ e : Ix p q ≃ Fin V.rank, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat (A.ε τ) e := by
  intro D V
  refine ⟨?_, fun A τ p q h => exists_signCompat (P := A.fr τ) (by rw [A.fr_gram]; exact h)⟩
  choose ε P h1 h2 using fun τ => exists_signFrame (H := gramAt D V τ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  exact ⟨⟨ε, P, h1, h2⟩⟩

end GlobalTheory.FrameExists
