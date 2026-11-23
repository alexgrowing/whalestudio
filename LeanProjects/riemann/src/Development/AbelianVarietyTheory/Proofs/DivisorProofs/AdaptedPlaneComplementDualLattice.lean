import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.AdaptedPlaneDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J a (b + c) = form σ J a b + form σ J a c := by
  have : (fun i => σ ((b + c) i)) = (fun i => σ (b i)) + fun i => σ (c i) := by
    funext i; simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) (c : E) :
    form σ J a (c • b) = σ c * form σ J a b := by
  have : (fun i => σ ((c • b) i)) = σ c • fun i => σ (b i) := by
    funext i; simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_gram (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (y x : Fin n₁ → E) : form σ (ιᵀ * J * ι.map σ) y x = form σ J (ι *ᵥ y) (ι *ᵥ x) := by
  have hx : (fun i => σ ((ι *ᵥ x) i)) = ι.map σ *ᵥ fun i => σ (x i) := by
    funext i
    simpa [Function.comp_def] using RingHom.map_mulVec (σ : E →+* E) ι x i
  simp only [form, hx, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end GlobalTheory.AdaptedPlaneDual

namespace GlobalTheory.AdaptedPlaneDual

theorem dual_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → ∀ y, y ∈ W₁.L ↔ ∀ x ∈ W₁.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W₁.J y x)) := by
  intro F E _ _ _ _ _ σ B _ n n₁ W W₁ H i₀ i₁ r s hW hH y
  have hg : ∀ a b, form σ W₁.J a b = form σ W.J (H.ι *ᵥ a) (H.ι *ᵥ b) := by
    intro a b
    rw [← hH.gram]
    exact form_gram σ W.J H.ι a b
  constructor
  · intro hy x hx o
    rw [hg]
    exact (hW.dual (H.ι *ᵥ y)).1 ((hH.low y).1 hy) _ ((hH.low x).1 hx) o
  · intro h
    rw [hH.low, hW.dual]
    intro z hz o
    obtain ⟨s', t, u, -, -, hu, rfl⟩ := hH.split z hz
    have h0 : form σ W.J (H.ι *ᵥ y) (s' • H.x + H.ι *ᵥ u + t • H.y) = form σ W₁.J y u := by
      rw [form_add_right, form_add_right, form_smul_right, form_smul_right, (hH.orth y).1, (hH.orth y).2, hg]
      ring
    rw [h0]
    exact h u hu o

end GlobalTheory.AdaptedPlaneDual
