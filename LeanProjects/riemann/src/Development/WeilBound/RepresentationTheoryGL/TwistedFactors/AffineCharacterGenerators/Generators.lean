import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar

noncomputable section

open MvPolynomial Filter Topology

namespace PositivityTheory.Rg.Fx

def Killing : Prop :=
  ∀ (ι κ B : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype B] (W : Subgroup (Equiv.Perm ι))
    (b : B → Fam ι κ) (Λ₀ : ι → ℂ) (h₀ : κ → ℂ), (∀ w ∈ W, ∀ i, ¬ (b i).Mem (Λ₀ ∘ w) h₀) →
    ∃ F : KF ι κ, (∀ w ∈ W, map (ren (w : ι → ι)) F = F) ∧ (∀ i, (b i).sub F = 0) ∧ evK Λ₀ h₀ F ≠ 0

def Pieces : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : EP ι), (∀ k, (piece k f).IsHomogeneous k) ∧
    (∃ K : ℝ, ∀ k, l1 (piece k f) ≤ K ^ (k + 1) / k.factorial) ∧
    (∀ Λ, HasSum (fun k => eval Λ (piece k f)) (ev Λ f)) ∧
    ∀ (ι' : Type) [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (k : ℕ), piece k (ren δ f) = rename δ (piece k f)

def Subst : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (Λ₀ : ι → ℂ) (M : Matrix ι ι' ℝ) (f : EP ι),
    (∀ lam : ι' → ℂ, ev lam (aff Λ₀ M f) = ev (fun i => Λ₀ i + ∑ j, (M i j : ℂ) * lam j) f) ∧
    ∀ (ι'' : Type) [Fintype ι''] (Λ₁ : ι' → ℂ) (N : Matrix ι' ι'' ℝ),
      aff Λ₁ N (aff Λ₀ M f) = aff (fun i => Λ₀ i + ∑ j, (M i j : ℂ) * Λ₁ j) (M * N) f

def Generators : Prop :=
  ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ), ∃ K : ℝ, ∀ (k : ℕ) (P : MvPolynomial (τ × Fin n) ℂ),
    P.totalDegree ≤ k → (∀ w : τ → Equiv.Perm (Fin n), rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) P = P) →
    ∃ G : MvPolynomial (τ × Fin n) ℂ, aeval blockE G = P ∧ G.totalDegree ≤ k ∧ l1 G ≤ K ^ (k + 1) * l1 P

def Rearrange : Prop :=
  ∀ (ι κ : Type) [Fintype ι] (b : Fam ι κ) (A M : Type) [CommRing A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
    [Module A M] [IsScalarTower ℂ A M] (D : Fin b.r → A) (τ : Multiplicative (Fin b.r → ℝ) →* A) (φ : M →ₗ[ℂ] ℂ),
    (∀ (v : Fin b.r → ℝ) (m : M), HasSum
      (fun k : ℕ => (k.factorial : ℂ)⁻¹ * φ ((∑ j, (v j : ℂ) • D j) ^ k • m)) (φ (τ (Multiplicative.ofAdd v) • m))) →
    ∀ (F : KF ι κ) (m : M), HasSum
      (fun k => φ (eval₂ (aeval fun i => algebraMap ℂ A (b.Λ i) + ∑ j, (b.emb i j : ℂ) • D j).toRingHom
        (fun k' => lift D τ (b.h k')) (pieceK k F) • m))
      (φ (lift D τ (b.sub F) • m))

def Separate : Prop :=
  ∀ (η : ℝ), 0 < η → ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
    Function.Injective (fun i => (a i, ζ i)) → ∃ (s₀ : ℕ) (K : ℝ), ∀ (m j : ℕ) (c : I → ℂ) (ε : ℝ),
      (∀ s ≤ s₀, ∀ s' ≤ s₀, ‖∑ i, c i * (cheb η (m + s) (a i) : ℂ) * ζ i ^ (j + s')‖ ≤ ε) →
      ∀ i, ‖c i‖ * (2 * a i / η - 1) ^ m * ‖ζ i‖ ^ j ≤ K * ε

def Degree : Prop :=
  ∃ d : ℕ → ℕ, Tendsto (fun j => (d j : ℝ) / j) atTop (𝓝 0) ∧
    ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial

def Exponents : Prop :=
  ∀ (d : ℕ → ℕ), Tendsto (fun j => (d j : ℝ) / j) atTop (𝓝 0) →
    (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
    ∀ (p : ℕ), 0 < p → ∀ (c₁ cq a₀ : ℝ), 0 < a₀ → a₀ ≤ 1 → ∃ η : ℝ, 0 < η ∧ η < a₀ ∧ ∃ N : ℝ,
      ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, Real.exp (-cq) ≤ ‖ζ i‖) →
      Function.Injective (fun i => (a i, ζ i)) → ∀ (c : ℕ → I → ℂ) (c' : I → ℂ),
      (∀ i, Tendsto (fun j => c j i) atTop (𝓝 (c' i))) →
      (∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ s ≤ s₀, ∀ s' ≤ s₀,
        ‖∑ i, c j i * (a i : ℂ) ^ d j * (cheb η (j / p + s) (a i) : ℂ) * ζ i ^ (j + s')‖ ≤
          K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) +
            (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      ∀ i, a₀ ≤ a i → c' i = 0

end PositivityTheory.Rg.Fx
