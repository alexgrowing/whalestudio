import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists

open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta

noncomputable section

namespace GlobalTheory.Published

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DiscreteSeriesExists : Prop := DiscreteSeriesUpqExists

theorem discreteSeriesExists_iff_upq : DiscreteSeriesExists ↔ DiscreteSeriesUpqExists := Iff.rfl

theorem discreteSeriesExists_iff : DiscreteSeriesExists ↔
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ := Iff.rfl

theorem exists_frame_of_hasSignature {n p q : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Formalism.UG.HasSignature J p q)
    (ε : Fin n → Bool) (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, IsUnit A ∧ Aᴴ * Formalism.REAL.Jm ε * A = J := by
  classical
  have cp : Fintype.card {a // ε a = true} = p := by rw [Fintype.card_subtype]; exact hp
  have cq : Fintype.card {a // ¬ ε a = true} = q := by
    rw [Fintype.card_subtype, ← hq]; simp
  let e' : Fin p ⊕ Fin q ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFinOfCardEq cp).symm (Fintype.equivFinOfCardEq cq).symm).trans
      (Equiv.sumCompl fun a => ε a = true)
  have hl : ∀ i, ε (e' (Sum.inl i)) = true := fun i => ((Fintype.equivFinOfCardEq cp).symm i).2
  have hr : ∀ i, ¬ ε (e' (Sum.inr i)) = true := fun i => ((Fintype.equivFinOfCardEq cq).symm i).2
  have hJm : Formalism.REAL.Jm ε = (Formalism.UG.Jpq p q).submatrix e'.symm e'.symm := by
    ext a b
    obtain ⟨x, rfl⟩ := e'.surjective a
    obtain ⟨y, rfl⟩ := e'.surjective b
    simp only [Formalism.REAL.Jm, Formalism.UG.Jpq, submatrix_apply, Equiv.symm_apply_apply, diagonal_apply,
      EmbeddingLike.apply_eq_iff_eq]
    rcases x with x | x <;> rcases y with y | y <;> simp [hl, hr, Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨e, Q, hQ⟩ := hJ
  have hQ' : (Q : Matrix _ _ ℂ)ᴴ * J.reindex e e * (Q : Matrix _ _ ℂ) = Formalism.UG.Jpq p q := hQ
  have h1 : ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)ᴴ * Formalism.UG.Jpq p q * ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) =
      J.reindex e e := by
    rw [← hQ']
    calc _ = ((Q : Matrix _ _ ℂ) * ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ))ᴴ * J.reindex e e *
          ((Q : Matrix _ _ ℂ) * ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv]; simp
  refine ⟨((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ).submatrix e'.symm e, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one ((Q : Matrix _ _ ℂ).submatrix e e'.symm) ?_
    rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]
  · rw [hJm, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1]
    simp

theorem dsExists_of_discreteSeriesExists (h : DiscreteSeriesExists) :
    ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar), Formalism.IndefR.Mult.DSExists V S := by
  intro D V S hV hS
  choose lam ε hE hP hp hq using hS
  choose H i1 i2 σ hσ using fun τ => discreteSeriesExists_iff.1 h V.rank (ε τ) (lam τ) (hP τ)
  choose A hA hG using fun τ => exists_frame_of_hasSignature (hV (tauE D τ)) (ε τ) (hp τ) (hq τ)
  exact ⟨@Formalism.IndefR.Mult.DSModel.mk D V S H i1 i2 σ lam ε A hE hσ hA hG⟩

end GlobalTheory.Published
