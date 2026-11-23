import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.NondegTuple

theorem conj_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem exists_tuple_gram_det_ne_zero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ a : ℕ, a ≤ n → ∃ X0 : Fin a → Fin n → E, (gramE σ J X0).det ≠ 0 ∧
        ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j := by
  intro F E _ _ _ _ _ σ hσ n J hJ a ha
  have hc : ∀ t, (σ : E →+* E) ((σ : E →+* E) t) = t := conj_conj hσ
  obtain ⟨P, d, -, hd, hfix, hne⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    (G := J) two_ne_zero hc (fun i j => hJ.1 j i)
  have hg : gramE σ J (fun i k => σ (P k (Fin.castLE ha i))) =
      Matrix.diagonal fun i => d (Fin.castLE ha i) := by
    ext i j
    have h1 := congrFun (congrFun hd (Fin.castLE ha i)) (Fin.castLE ha j)
    rw [GlobalTheory.HermDiag.transpose_mul_mul_map_apply,
      GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum] at h1
    have h2 : Matrix.diagonal d (Fin.castLE ha i) (Fin.castLE ha j) =
        Matrix.diagonal (fun i => d (Fin.castLE ha i)) i j := by
      simp only [Matrix.diagonal_apply, (Fin.castLE_injective ha).eq_iff]
    rw [← h2, ← h1]
    simp only [gramE, hE, Formalism.UG.hform, RingHom.coe_coe, conj_conj hσ]
  refine ⟨fun i k => σ (P k (Fin.castLE ha i)), ?_, ?_⟩
  · rw [hg, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hne hJ.2 _
  · intro i j
    rw [hg]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact hfix _
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij), map_zero]

end GlobalTheory.NondegTuple
