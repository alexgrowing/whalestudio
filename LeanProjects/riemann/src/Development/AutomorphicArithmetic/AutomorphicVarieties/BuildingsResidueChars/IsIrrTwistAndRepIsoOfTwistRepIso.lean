import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.isIrr_twist_and_repIso_of_twist_repIso :
    ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (χ : Γ →* kˣ), (∀ r : Γ →* GL (Fin n) k, IsIrr r → IsIrr (tw r χ)) ∧ ∀ r r' : Γ →* GL (Fin n) k, RepIso (tw r χ) (tw r' χ) → RepIso r r' := by
  intro Γ k _ _ n χ
  have key : ∀ (r : Γ →* GL (Fin n) k) W, IsInv (tw r χ) W ↔ IsInv r W := fun r W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  refine ⟨fun r hr => ?_, fun r r' ⟨g, hg⟩ => ⟨g, fun s => ?_⟩⟩
  · unfold IsIrr IsIrrSub at hr ⊢
    simpa only [key] using hr
  · have h := congrArg Units.val (hg s)
    apply Units.ext
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul] at h ⊢
    exact smul_right_injective _ (Units.ne_zero (χ s)) h
