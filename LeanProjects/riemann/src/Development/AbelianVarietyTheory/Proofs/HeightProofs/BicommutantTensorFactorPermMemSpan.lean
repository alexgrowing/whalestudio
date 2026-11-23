import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem bicomm_left_mul {ι G : Type} [Fintype ι] [DecidableEq ι] (ρ : G → Matrix ι ι ℂ)
    (p : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) (hp : ∀ g X, p (ρ g * X) = ρ g * p X) (M : Matrix ι ι ℂ)
    (hM : ∀ T : Matrix ι ι ℂ, (∀ g, T * ρ g = ρ g * T) → M * T = T * M) (X : Matrix ι ι ℂ) :
    p (M * X) = M * p X := by
  have key : ∀ (A : Matrix ι ι ℂ) (i j a b : ι),
      ((Matrix.of fun a b => p (Matrix.single b i 1) a j) * A) a b = p (A * Matrix.single b i 1) a j := by
    intro A i j a b
    have : A * Matrix.single b i 1 = ∑ c, A c b • Matrix.single c i (1 : ℂ) := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.single_apply, smul_eq_mul]
      by_cases h : i = y <;> simp [h]
    rw [this, map_sum]
    simp only [Matrix.mul_apply, Matrix.sum_apply, map_smul, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_comm]
  have key2 : ∀ (A : Matrix ι ι ℂ) (i j a b : ι),
      (A * (Matrix.of fun a b => p (Matrix.single b i 1) a j)) a b = (A * p (Matrix.single b i 1)) a j := by
    intro A i j a b
    simp [Matrix.mul_apply]
  have h1 : ∀ b i, p (M * Matrix.single b i 1) = M * p (Matrix.single b i 1) := by
    intro b i
    ext a j
    rw [← key, ← key2, hM]
    intro g
    ext a b
    rw [key, key2, hp]
  have h2 : X = ∑ b, ∑ i, X b i • Matrix.single b i (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  rw [h2]
  simp only [Matrix.mul_sum, map_sum, Matrix.mul_smul, map_smul, h1]

theorem bicomm_mem_span {ι G : Type} [Fintype ι] [DecidableEq ι] [Group G] [Fintype G] (ρ : G → Matrix ι ι ℂ)
    (h1 : ρ 1 = 1) (hmul : ∀ g h, ρ g * ρ h = ρ (h * g)) (M : Matrix ι ι ℂ)
    (hM : ∀ T : Matrix ι ι ℂ, (∀ g, T * ρ g = ρ g * T) → M * T = T * M) :
    M ∈ Submodule.span ℂ (Set.range ρ) := by
  set B := Submodule.span ℂ (Set.range ρ) with hB
  have hst : ∀ g, ∀ X ∈ B, ρ g * X ∈ B := by
    intro g X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hmul]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add]; exact B.add_mem hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact B.smul_mem c hx
  obtain ⟨q, hq⟩ := LinearMap.exists_extend (LinearMap.id : B →ₗ[ℂ] B)
  have hq' : ∀ X ∈ B, (q X : Matrix ι ι ℂ) = X := fun X hX => by
    have := LinearMap.congr_fun hq ⟨X, hX⟩
    exact congrArg Subtype.val this
  let p : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    ∑ g : G, LinearMap.mulLeft ℂ (ρ g⁻¹) ∘ₗ B.subtype ∘ₗ q ∘ₗ LinearMap.mulLeft ℂ (ρ g)
  have hp : ∀ X, p X = ∑ g : G, ρ g⁻¹ * (q (ρ g * X) : Matrix ι ι ℂ) := fun X => by
    simp [p, LinearMap.sum_apply]
  have hpB : ∀ X, p X ∈ B := fun X => by
    rw [hp]
    exact B.sum_mem fun g _ => hst _ _ (q _).2
  have hone : (1 : Matrix ι ι ℂ) ∈ B := Submodule.subset_span ⟨1, h1⟩
  have hp1 : p 1 = (Fintype.card G : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [hp]
    have : ∀ g : G, ρ g⁻¹ * (q (ρ g * 1) : Matrix ι ι ℂ) = 1 := fun g => by
      rw [hq' _ (hst _ _ hone), mul_one, hmul, mul_inv_cancel, h1]
    simp only [this]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hpρ : ∀ h X, p (ρ h * X) = ρ h * p X := fun h X => by
    rw [hp, hp, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft]
    rw [← mul_assoc, hmul, ← mul_assoc, hmul]
    simp
  have := bicomm_left_mul ρ p hpρ M hM 1
  rw [hp1, mul_one, Matrix.mul_smul, mul_one] at this
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h3 := B.smul_mem (Fintype.card G : ℂ)⁻¹ (hpB M)
  rwa [this, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3

theorem bicomm_permMat : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
  intro n d M hM
  refine bicomm_mem_span (permMat n d) ?_ ?_ M hM
  · ext I K
    simp [permMat, Matrix.one_apply]
  · intro g h
    ext I K
    simp only [permMat, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (K ∘ h)]
    · rw [if_pos rfl, mul_one]
      rfl
    · intro J _ hJ
      simp [hJ]
    · simp

end GlobalTheory.SmoothForms
