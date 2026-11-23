import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.SimplexMem

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

def PLoc : Prop := Hyp U A φ → ∀ h ∈ U, ∃ s : Finset Γ, ∃ W ∈ 𝓝 h, W ⊆ U ∧
  ∀ γ ∉ s, ∀ x ∈ W, psi A φ γ x = 0

def PHom : Prop := Hyp U A φ → ∀ (q n : ℕ) (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (σ : ℕ → Γ),
  ∀ h ∈ U, delG n (Kf A φ β) σ h = β σ h - Kf A φ (delG (n + 1) β) σ h

def PSmooth : Prop := Hyp U A φ → ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ : ℕ → Γ),
  ContDiffOn ℝ (⊤ : ℕ∞) (eta A φ c j σ) U ∧ ContDiffOn ℝ (⊤ : ℕ∞) (Kf A φ (eta A φ c j) σ) U

def PClosed : Prop := Hyp U A φ → ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ : ℕ → Γ),
  ∀ h ∈ U, extDeriv (eta A φ c j σ) h = 0

def PDep : Prop := ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ σ' : ℕ → Γ),
  (∀ n, n + j ≤ k + 1 → σ n = σ' n) → eta A φ c j σ = eta A φ c j σ'

def PCoc : Prop := Hyp U A φ → ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ), Coc c → ∀ j ≤ k + 1,
  ∀ (σ : ℕ → Γ), ∀ h ∈ U, delG (k + 1 - j) (eta A φ c j) σ h = 0

def PEquiv : Prop := Hyp U A φ → ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ), (∀ g y, c (fun j => g * y j) = c y) →
  ∀ (B : V →L[ℝ] V) (a : Γ), (∀ h ∈ U, B h ∈ U) → (∀ γ, ∀ h ∈ U, psi A φ γ (B h) = psi A φ (a * γ) h) →
  ∀ (j : ℕ) (σ : ℕ → Γ), ∀ h ∈ U,
    (eta A φ c j σ (B h)).compContinuousLinearMap B = eta A φ c j (fun n => a * σ n) h ∧
    (Kf A φ (eta A φ c j) σ (B h)).compContinuousLinearMap B = Kf A φ (eta A φ c j) (fun n => a * σ n) h

def PBound : Prop := Hyp U A φ → ∀ O : Set Γ, O.Finite →
  (∀ γ, ∀ h : U, h ∈ closure {x : U | φ x ≠ 0} → ∀ hm : A γ⁻¹ h ∈ U,
    (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0} → γ ∈ O) →
  (∃ C, ∀ h ∈ U, |φ h| ≤ C) →
  ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ), Coc c → ∃ C, ∀ h ∈ U, ∀ (T : V →L[ℝ] V) (M : ℝ), 0 ≤ M →
    (∀ γ, ‖(fderiv ℝ (psi A φ γ) h).comp T‖ ≤ M) →
    ‖(eta A φ c (k + 1) (fun _ => 1) h).compContinuousLinearMap T‖ ≤ C * M ^ (k + 1)

def PComp : Prop := Hyp U A φ →
  (∀ (q : ℕ) (ω : V → V [⋀^Fin q]→L[ℝ] ℝ), ContDiffOn ℝ 1 ω U → ∀ y : Fin (q + 2) → V, (∀ j, y j ∈ U) →
     dC' (intS' ω) y = intS' (extDeriv ω) y) →
  ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ), Coc c → ∀ o ∈ U, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
  ∃ b : (Fin (k + 1) → Γ) → ℝ, (∀ g y, b (fun j => g * y j) = b y) ∧
    ∀ g : Fin (k + 2) → Γ, c g = s * intS' (eta A φ c (k + 1) fun _ => 1) (fun l => A (g l) o) + dC' b g

end PositivityTheory.KB.WhittakerCocycle

end
