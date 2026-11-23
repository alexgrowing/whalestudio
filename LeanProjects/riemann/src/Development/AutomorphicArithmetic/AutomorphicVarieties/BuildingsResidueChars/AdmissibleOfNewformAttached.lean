import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.admissible_of_newform_attached :
    NewformAut → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e M : ℕ), 1 ≤ e → ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), IsIrr W → (∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) → Level l M ![(e : ℤ), -(e : ℤ)] W → IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → AdmR ι M ![(e : ℤ), -(e : ℤ)] 0 W := by
  intro hN Ω _ _ _ l _ ι e M he W hirr hf hlev hcyc
  obtain ⟨f, hf⟩ := hf
  refine ⟨hirr, hN (2 * e + 1) (by omega) f l Ω ι W _ hf, hlev, ⟨_, hcyc, ?_⟩,
    Or.inr fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega⟩
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two]), fun s => ?_⟩
  simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  generalize ((W s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.vecMul, dotProduct] <;> ring
