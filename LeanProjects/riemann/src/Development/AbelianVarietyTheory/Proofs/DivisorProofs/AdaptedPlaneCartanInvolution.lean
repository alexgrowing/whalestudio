import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CartanRestrict

theorem isCartan_restrict {n m : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} {θ₁ : Matrix (Fin m) (Fin m) ℂ}
    {ι : Matrix (Fin n) (Fin m) ℂ} {L : Matrix (Fin m) (Fin n) ℂ} (hL : L * ι = 1) (h : IsCartan M θ)
    (hι : θ * ι = ι * θ₁) : IsCartan (ιᵀ * M * ι.map star) θ₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (C : Matrix (Fin b) (Fin c) ℂ),
      (A * C).map star = A.map star * C.map star := fun A C => Matrix.map_mul (f := starRingEnd ℂ)
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · have : ι * (θ₁ * θ₁) = ι := by
      rw [← Matrix.mul_assoc, ← hι, Matrix.mul_assoc, ← hι, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    calc θ₁ * θ₁ = L * (ι * (θ₁ * θ₁)) := by rw [← Matrix.mul_assoc L, hL, Matrix.one_mul]
      _ = 1 := by rw [this, hL]
  · calc θ₁ᵀ * (ιᵀ * M * ι.map star) * θ₁.map star
        = (ι * θ₁)ᵀ * M * (ι * θ₁).map star := by
          rw [hs, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = ιᵀ * (θᵀ * M * θ.map star) * ι.map star := by
          rw [← hι, hs, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2]
  · have hx' : ι *ᵥ x ≠ 0 := fun h0 => hx (by
      have : L *ᵥ (ι *ᵥ x) = 0 := by rw [h0, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] at this)
    have hst : star (ι *ᵥ x) = ι.map star *ᵥ star x := by
      ext i
      simp [Matrix.mulVec, dotProduct]
    have := h3 _ hx'
    rw [hst, Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    exact this

theorem isCartan_of_isAdapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ r' s' i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), B.IsGood σ → W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ w : InfinitePlace F,
    (∃ L : Matrix (Fin d₁) (Fin d) ℂ, L * H'.ι.map (B.emb w).1 = 1) →
      IsCartan (Complex.I • W₁.J.map (B.emb w).1) (W₁.θ w) := by
  intro F E _ _ _ _ _ σ B d d₁ r' s' i₀ i₁ W W₁ H' hB hW hH w ⟨L, hL⟩
  have key := isCartan_restrict hL (hW.cartan w) (hH.cartan w).1
  have hc : (H'.ι.map σ).map (B.emb w).1 = (H'.ι.map (B.emb w).1).map star := by
    ext i j
    simpa using hB.cm.2.2.2 (B.emb w).1 (H'.ι i j)
  have hg : W₁.J.map (B.emb w).1 =
      (H'.ι.map (B.emb w).1)ᵀ * W.J.map (B.emb w).1 * (H'.ι.map (B.emb w).1).map star := by
    rw [← hH.gram, Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map]
  rw [hg, ← Matrix.smul_mul, ← Matrix.mul_smul]
  exact key

end GlobalTheory.CartanRestrict
