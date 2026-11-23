import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma beta_baseChange {E : Type} [Field E] [NumberField E] {n : ℕ}
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) (b : 𝓞 E)
    (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    β ((DistribMulAction.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ z) = (b : E) • β z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul q v =>
    have h1 : ∀ w : Fin n → 𝓞 E, q ⊗ₜ[ℤ] w = q • ((1 : ℚ) ⊗ₜ[ℤ] w) := by
      intro w
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : (DistribMulAction.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ (q ⊗ₜ[ℤ] v)
        = q ⊗ₜ[ℤ] (b • v) := by
      rw [LinearMap.baseChange_tmul]
      rfl
    rw [h2, h1 (b • v), h1 v, map_smul, map_smul]
    funext i
    simp only [Pi.smul_apply, hβ]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingOfIntegers.coe_eq_algebraMap, Rat.smul_def, mul_left_comm, Algebra.smul_def]

theorem UpperTheory.Gal.W2.Seed.pRepLaws :
    RepLaws := by
  rintro E _ _ _ A n rep ⟨β, hβ, hr⟩
  have hβ1 : ∀ v : Fin n → 𝓞 E, β (1 ⊗ₜ v) = fun i => (v i : E) := fun v => funext (hβ v)
  have hsc : ∀ c : 𝓞 E, rep (algebraMap E (Matrix (Fin n) (Fin n) E) c)
      = (DistribMulAction.toLinearMap ℤ (Fin n → 𝓞 E) c).baseChange ℚ := by
    intro c
    refine LinearMap.ext fun z => β.injective ?_
    rw [hr, beta_baseChange β hβ c z, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  refine ⟨?_, ?_, hsc, ?_⟩
  · intro x y hxy
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := β.surjective w
    simp only [Matrix.toLin'_apply]
    rw [← hr, ← hr, hxy]
  · intro M
    constructor
    · rintro ⟨x, rfl⟩ b
      rw [← hsc, ← map_mul, ← map_mul, Algebra.commutes]
    · intro hM
      let F0 : (Fin n → E) →ₗ[ℚ] (Fin n → E) := β.toLinearMap ∘ₗ M ∘ₗ β.symm.toLinearMap
      have hF0 : ∀ (b : 𝓞 E) w, F0 ((b : E) • w) = (b : E) • F0 w := by
        intro b w
        obtain ⟨z, rfl⟩ := β.surjective w
        have h := congrArg (fun N => β (N z)) (hM b)
        simp only [Module.End.mul_apply] at h
        rw [beta_baseChange β hβ] at h
        simp only [F0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        rw [← beta_baseChange β hβ, LinearEquiv.symm_apply_apply, h]
      have hF : ∀ (e : E) w, F0 (e • w) = e • F0 w := by
        intro e w
        obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
        have hd0 : (algebraMap (𝓞 E) E d) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
        apply smul_right_injective (Fin n → E) hd0
        change algebraMap (𝓞 E) E d • F0 _ = algebraMap (𝓞 E) E d • _
        rw [smul_smul, mul_div_cancel₀ _ hd0]
        have h2 := hF0 d ((algebraMap (𝓞 E) E b / algebraMap (𝓞 E) E d) • w)
        have h3 := hF0 b w
        change F0 (algebraMap (𝓞 E) E d • _) = algebraMap (𝓞 E) E d • _ at h2
        change F0 (algebraMap (𝓞 E) E b • _) = algebraMap (𝓞 E) E b • _ at h3
        rw [← h2, smul_smul, mul_div_cancel₀ _ hd0, h3]
      let F : (Fin n → E) →ₗ[E] (Fin n → E) :=
        { toFun := F0, map_add' := F0.map_add, map_smul' := hF }
      refine ⟨Matrix.toLin'.symm F, ?_⟩
      refine LinearMap.ext fun z => β.injective ?_
      rw [hr]
      have hx : (Matrix.toLin'.symm F) *ᵥ β z = F (β z) := by
        rw [← Matrix.toLin'_apply, LinearEquiv.apply_symm_apply]
      rw [hx]
      simp [F, F0]
  · intro x v
    apply β.injective
    rw [hr, hβ1, hβ1]
    funext i
    exact (RingHom.map_mulVec (algebraMap (𝓞 E) E) x v i).symm
