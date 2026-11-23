import Mathlib

namespace GlobalTheory.ConjugateAlgebraLemmas

open Matrix

def conjAlg {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K where
  toFun M := ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K)
  map_one' := by simp
  map_mul' M N := by
    have h : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M * N) * (g : Matrix (Fin n) (Fin n) K)
        = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * ((g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * N * (g : Matrix (Fin n) (Fin n) K) := by rw [h, Matrix.mul_one, Matrix.mul_assoc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M N]
      _ = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K) * (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N * (g : Matrix (Fin n) (Fin n) K)) := by simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    have h : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h]

theorem conjAlg_apply {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K) :
    conjAlg g M = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K) := rfl

theorem aeval_conj {K : Type} [Field K] {n : ℕ} (γ g : GL (Fin n) K) (Q : Polynomial K) :
    Polynomial.aeval ((↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K)) Q
      = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K) := by
  have h : ((↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K)) = conjAlg g (γ : Matrix (Fin n) (Fin n) K) := by
    rw [conjAlg_apply, Units.val_mul, Units.val_mul]
  rw [h, Polynomial.aeval_algHom_apply, conjAlg_apply]

theorem gram_eq {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : (g.map σ)ᵀ * g = 1) (a b : Fin n → K) :
    ∑ k : Fin n, σ ((g *ᵥ a) k) * (g *ᵥ b) k = ∑ k : Fin n, σ (a k) * b k := by
  have h1 : ∀ k, σ ((g *ᵥ a) k) = ((g.map σ) *ᵥ (fun i => σ (a i))) k := by
    intro k
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp_rw [h1]
  change (g.map σ *ᵥ fun i => σ (a i)) ⬝ᵥ (g *ᵥ b) = (fun i => σ (a i)) ⬝ᵥ b
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hg, Matrix.vecMul_one]

theorem main : ∀ {K : Type} [inst : Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K), Matrix.transpose (Matrix.map (↑g : Matrix (Fin n) (Fin n) K) (⇑σ : K → K)) * (↑g : Matrix (Fin n) (Fin n) K) = (1 : Matrix (Fin n) (Fin n) K) → ∀ (Q : Polynomial K) {ι : Type} (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker ((Matrix.toLin' : Matrix (Fin n) (Fin n) K → (Fin n → K) →ₗ[K] Fin n → K) ((Polynomial.aeval (↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K) : Polynomial K → Matrix (Fin n) (Fin n) K) Q)) → (LinearIndependent K fun (i : ι) ↦ Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i)) ∧ Submodule.span K (Set.range fun (i : ι) ↦ Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i)) = LinearMap.ker ((Matrix.toLin' : Matrix (Fin n) (Fin n) K → (Fin n → K) →ₗ[K] Fin n → K) ((Polynomial.aeval (↑γ : Matrix (Fin n) (Fin n) K) : Polynomial K → Matrix (Fin n) (Fin n) K) Q)) ∧ ((Matrix.of : (ι → ι → K) → Matrix ι ι K) fun (i j : ι) ↦ ∑ k : Fin n, (σ : K → K) (Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i) k) * Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u j) k) = (Matrix.of : (ι → ι → K) → Matrix ι ι K) fun (i j : ι) ↦ ∑ k : Fin n, (σ : K → K) (u i k) * u j k := by
  intro K _ σ n γ g hg Q ι u hu hspan
  have hgg : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨?_, ?_, ?_⟩
  · have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) := by
      intro x y hxy
      have h := congrArg (fun z => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) hxy
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hgg'] using h
    exact hu.map' (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) (LinearMap.ker_eq_bot.mpr hinj)
  · have hmap : Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
        (Submodule.span K (Set.range u)).map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap, hspan, aeval_conj]
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      calc Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x)
          = (g : Matrix (Fin n) (Fin n) K) *ᵥ ((((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K)) *ᵥ x) := by
            simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
        _ = 0 := by rw [hx, Matrix.mulVec_zero]
    · intro hy
      refine ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y, ?_, ?_⟩
      · calc (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K)) *ᵥ
              (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y)
            = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
              (Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q *ᵥ y) := by
              simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hgg, Matrix.mul_one]
          _ = 0 := by rw [hy, Matrix.mulVec_zero]
      · rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  · ext i j
    simp only [Matrix.of_apply]
    exact gram_eq σ (g : Matrix (Fin n) (Fin n) K) hg (u i) (u j)

end GlobalTheory.ConjugateAlgebraLemmas
