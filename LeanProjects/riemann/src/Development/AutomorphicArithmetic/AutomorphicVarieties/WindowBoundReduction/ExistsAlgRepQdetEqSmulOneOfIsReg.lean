import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

theorem UpperTheory.exists_algRep_qdet_eq_smul_one_of_isReg :
    ∀ (E : Type) [Field E] [NumberField E] (a D : ℕ), 0 < D → ∀ (ρ : GL (Fin a) (Cinf E) →* Matrix (Fin D) (Fin D) ℂ), IsReg ρ → ∀ s : (E →+* ℂ) → ℂ → ℂ, (∀ τ u, Formalism.REAL.qdet (eOf ρ τ) u = s τ u • 1) → ∃ Ξ : AlgRep E a, ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = s τ u • 1 := by
  intro E _ _ a D hD ρ hreg s hs
  obtain ⟨d, A, B, σ, hd, -, hBA, hσ, hint, hirr⟩ := UpperTheory.V.Weyl.irrSub _ D ρ hD
  have hσreg : IsReg σ := by simpa only [← hσ] using isReg_conj hreg B A
  refine ⟨⟨d, σ, hσreg, hd, hirr⟩, fun τ u => ?_⟩
  have hlie : ∀ i j, eOf ρ τ i j * A = A * eOf σ τ i j := by
    intro i j
    have l := eOf_conj hreg (1 : Matrix (Fin D) (Fin D) ℂ) A τ i j
    have r := eOf_conj hσreg A (1 : Matrix (Fin d) (Fin d) ℂ) τ i j
    simp only [Matrix.one_mul, Matrix.mul_one, hint] at l r
    exact l.symm.trans r
  have hq := UpperTheory.V.Weyl.qdetRect a D d _ _ A hlie u
  calc Formalism.REAL.qdet (eOf σ τ) u = B * (A * Formalism.REAL.qdet (eOf σ τ) u) := by
        rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
    _ = s τ u • 1 := by
        rw [← hq, hs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hBA]
