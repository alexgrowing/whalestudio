import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SkewPlane

theorem star_mulVec' {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (x : Fin k → ℂ) :
    star (A *ᵥ x) = A.map star *ᵥ star x := by
  ext i; simp [Matrix.mulVec, dotProduct, star_sum]

theorem map_star_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (C : Matrix (Fin b) (Fin c) ℂ) :
    (A * C).map star = A.map star * C.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem cartan_compl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → ∀ P : Matrix (Fin n₁) (Fin n) E, P * H.ι = 1 →
    ∀ w, IsCartan (Complex.I • W₁.J.map (B.emb w).1) (W₁.θ w) := by
  intro F E _ _ _ _ _ σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH P hP w
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hcm : ∀ z : E, τ (σ z) = star (τ z) := fun z => hB.cm.2.2.2 τ z
  set ι' : Matrix (Fin n) (Fin n₁) ℂ := H.ι.map τ with hι'
  set P' : Matrix (Fin n₁) (Fin n) ℂ := P.map τ with hP'
  have hPι : P' * ι' = 1 := by
    rw [hP', hι', ← Matrix.map_mul, hP, Matrix.map_one τ (map_zero τ) (map_one τ)]
  set M : Matrix (Fin n) (Fin n) ℂ := Complex.I • W.J.map τ with hM
  have hσ : (H.ι.map σ).map τ = ι'.map star := by
    ext i j; simp [hι', hcm]
  have hM₁ : Complex.I • W₁.J.map τ = ι'ᵀ * M * ι'.map star := by
    rw [← hH.gram, Matrix.map_mul, Matrix.map_mul, hσ, hM, Matrix.transpose_map, ← hι',
      Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨c1, c2, c3⟩ := hW.cartan w
  set θ := W.θ w
  set θ₁ := W₁.θ w
  have hc : θ * ι' = ι' * θ₁ := (hH.cartan w).1
  rw [hM₁]
  refine ⟨?_, ?_, ?_⟩
  · have e0 : θ * θ * ι' = ι' * θ₁ * θ₁ := by
      rw [Matrix.mul_assoc θ θ ι', hc, ← Matrix.mul_assoc, hc]
    calc θ₁ * θ₁ = P' * (ι' * θ₁ * θ₁) := by
          rw [Matrix.mul_assoc ι', ← Matrix.mul_assoc P', hPι, Matrix.one_mul]
      _ = 1 := by rw [← e0, c1, Matrix.one_mul, hPι]
  · have e1 : θ₁ᵀ * (ι'ᵀ * M * ι'.map star) * θ₁.map star
        = (θ * ι')ᵀ * M * (θ * ι').map star := by
      rw [hc, Matrix.transpose_mul, map_star_mul]; simp only [Matrix.mul_assoc]
    rw [e1, Matrix.transpose_mul, map_star_mul]
    calc ι'ᵀ * θᵀ * M * (θ.map star * ι'.map star) = ι'ᵀ * (θᵀ * M * θ.map star) * ι'.map star := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [c2]
  · intro x hx
    have hx' : ι' *ᵥ x ≠ 0 := by
      intro h0; apply hx
      have := congrArg (P' *ᵥ ·) h0
      simpa [Matrix.mulVec_mulVec, hPι] using this
    have key : (θ₁ *ᵥ x) ⬝ᵥ (ι'ᵀ * M * ι'.map star) *ᵥ star x = (θ *ᵥ (ι' *ᵥ x)) ⬝ᵥ M *ᵥ star (ι' *ᵥ x) := by
      have h : θ *ᵥ (ι' *ᵥ x) = ι' *ᵥ (θ₁ *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
      rw [star_mulVec', h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (θ₁ *ᵥ x) ι'ᵀ,
        Matrix.vecMul_transpose]
    rw [key]; exact c3 _ hx'

end GlobalTheory.SkewPlane
