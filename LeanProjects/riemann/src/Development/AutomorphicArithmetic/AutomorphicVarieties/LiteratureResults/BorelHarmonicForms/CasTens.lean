import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ZalgCommute
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasXi
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cas_inter {E : Type} [Field E] [NumberField E] {a n : ℕ} (e : Fin n → Herm E a)
    {M N : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
    (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (L' : Lie E a →ₗ[ℝ] Module.End ℂ N) (f : M →ₗ[ℂ] N) (r : ℝ)
    (h : ∀ X m, f (L X m) = L' X (f m)) (m : M) :
    f (cas (shift L r) e m) = cas (shift L' r) e (f m) := by
  have h' : ∀ X m, f (shift L r X m) = shift L' r X (f m) := fun X m => by
    simp only [shift_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, h,
      LinearMap.map_smul_of_tower]
  simp only [cas, LinearMap.sum_apply, LinearMap.sub_apply, Module.End.mul_apply, map_sum, map_sub, h']

private theorem cas_alg {E : Type} [Field E] [NumberField E] {a n : ℕ} (e : Fin n → Herm E a)
    {A B : Type} [Ring A] [Algebra ℂ A] [Module ℝ A]
    [Ring B] [Algebra ℂ B] [Module ℝ B]
    (L : Lie E a →ₗ[ℝ] A) (L' : Lie E a →ₗ[ℝ] B) (f : A →ₐ[ℂ] B) (h : ∀ X, f (L X) = L' X) :
    f (cas L e) = cas L' e := by
  simp only [cas, map_sum, map_sub, map_mul, h]

theorem UpperTheory.V.Lit.Bor.casTens :
    UpperTheory.V.Lit.Bor.CasTens := by
  intro E _ _ _ a n e he π Ξ r
  obtain ⟨c₁, h₁⟩ := casPi E a n e he π r
  obtain ⟨c₂, h₂⟩ := casXi E a n e he Ξ (-r)
  have hB := cas_alg (B := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) e (shift Ξ.dmat (-r)) (shift (lieB π Ξ) (-r))
    ((Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) π.V).comp
      (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom)
    fun X => by
      rw [shift_apply, shift_apply, map_add, ← algebraMap_smul ℂ _ (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), map_smul, map_one]
      rfl
  rw [h₂, map_smul, map_one] at hB
  have hπ : ∀ φ : π.V, cas (A := Module.End ℂ π.V) (shift (lieOp π) r) e φ = c₁ • φ := fun φ =>
    Subtype.ext ((cas_inter e (lieOp π) (lie E a) π.V.subtype r (fun _ _ => rfl) φ).trans (h₁ φ.1 φ.2))
  have hA : ∀ m, cas (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (shift (lieA π Ξ) r) e m = c₁ • m := fun m => by
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | tmul φ v =>
      have h := cas_inter e (lieOp π) (lieA π Ξ) ((TensorProduct.mk ℂ π.V (Fin Ξ.d → ℂ)).flip v) r
        (fun _ _ => rfl) φ
      rw [hπ, map_smul] at h
      exact h.symm
  refine ⟨c₂ - c₁, fun m => ?_⟩
  rw [LinearMap.sub_apply, hA, ← hB]
  exact (sub_smul c₂ c₁ m).symm
