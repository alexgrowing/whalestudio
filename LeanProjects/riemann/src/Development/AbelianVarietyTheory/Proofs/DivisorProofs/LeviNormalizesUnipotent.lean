import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviNormUnip

theorem matMul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (g k : UA σ J) : mat (g * k) = mat g * mat k := rfl

theorem matOne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem matInvMul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  rw [← matMul, inv_mul_cancel, matOne]

theorem matMulInv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  rw [← matMul, mul_inv_cancel, matOne]

theorem levi_normalises_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h : UA σ G.V.J), IsLevi H l g₀ h →
    ∀ n ∈ unip σ G.V H, h * n * h⁻¹ ∈ unip σ G.V H := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ _ _ _ l g₀ h hL
  obtain ⟨hx, -, hι⟩ := hL

  have hx' : mat h⁻¹ *ᵥ incV F H.x = (l⁻¹).1 • incV F H.x := by
    have e1 : mat h⁻¹ *ᵥ (mat h *ᵥ incV F H.x) = incV F H.x := by
      rw [Matrix.mulVec_mulVec, matInvMul, Matrix.one_mulVec]
    rw [hx, Matrix.mulVec_smul] at e1
    calc mat h⁻¹ *ᵥ incV F H.x = ((l⁻¹).1 * l.1) • (mat h⁻¹ *ᵥ incV F H.x) := by
          rw [Units.inv_mul, one_smul]
      _ = (l⁻¹).1 • incV F H.x := by rw [mul_smul, e1]

  have hι' : mat h⁻¹ * incM F H.ι = incM F H.ι * mat g₀⁻¹ := by
    calc mat h⁻¹ * incM F H.ι = mat h⁻¹ * (incM F H.ι * mat g₀ * mat g₀⁻¹) := by
          rw [Matrix.mul_assoc (incM F H.ι), matMulInv, Matrix.mul_one]
      _ = mat h⁻¹ * (mat h * incM F H.ι) * mat g₀⁻¹ := by rw [hι]; simp only [Matrix.mul_assoc]
      _ = incM F H.ι * mat g₀⁻¹ := by
          rw [← Matrix.mul_assoc, matInvMul, Matrix.one_mul]
  intro n hn
  have key : ∀ u ∈ unip σ G.V H, h * u * h⁻¹ ∈ unip σ G.V H := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ => h * u * h⁻¹ ∈ unip σ G.V H) ?_ ?_ ?_ ?_ hu
    · intro u ⟨hu1, hu2⟩
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · rw [matMul, matMul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx', Matrix.mulVec_smul, hu1,
          Matrix.mulVec_smul, hx, smul_smul, Units.inv_mul, one_smul]
      · intro z
        obtain ⟨a, ha⟩ := hu2 (mat g₀⁻¹ *ᵥ z)
        refine ⟨l.1 * a, ?_⟩
        have e2 : mat h⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g₀⁻¹ *ᵥ z) := by
          rw [Matrix.mulVec_mulVec, hι', ← Matrix.mulVec_mulVec]
        have e3 : mat h *ᵥ (incM F H.ι *ᵥ (mat g₀⁻¹ *ᵥ z)) = incM F H.ι *ᵥ z := by
          rw [Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec]
          congr 1
          rw [Matrix.mulVec_mulVec, matMulInv, Matrix.one_mulVec]
        rw [matMul, matMul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, ha, Matrix.mulVec_add, e3,
          Matrix.mulVec_smul, hx, smul_smul, mul_comm]
    · simp
    · intro x y _ _ hx hy
      have := (unip σ G.V H).mul_mem hx hy
      simpa [mul_assoc] using this
    · intro x _ hx
      have := (unip σ G.V H).inv_mem hx
      simpa [mul_assoc] using this
  exact key n hn

end GlobalTheory.LeviNormUnip
