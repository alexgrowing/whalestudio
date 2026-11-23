import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTorsionFormPoint

set_option autoImplicit false

noncomputable section

open Matrix Set
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.TorsionForm

def IsDatum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ) : Prop :=
  IsPeriodMap B τ ∧ IsLat M ∧ IsFactor B τ M j ∧ IsMetric B τ M j h

def BaseChange : Prop :=
  ∀ (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E'] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsDatum B τ M j h → ∀ (B' : Set E') (φ : E' → E), IsOpen B' →
    DifferentiableOn ℂ φ B' → MapsTo φ B' B → ∀ (β : Fin n → E'), ∀ b ∈ B', ∀ T,
      IsTorsionForm (τ ∘ φ) M (fun l P => j l (φ P.1, P.2)) (fun P => h (φ P.1, P.2)) β b T ↔
        IsTorsionForm τ M j h (fun i => fderiv ℂ φ b (β i)) (φ b) T

def OneVector : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsDatum B τ M j h → ∀ (β : Fin n → E) (a : Fin n → ℂ), ∀ b ∈ B, ∀ T,
      IsTorsionForm τ M j h β b T → ∃ T', IsTorsionForm τ M j h ![∑ i, a i • β i] b T' ∧
        T' ∅ = T ∅ ∧
        T' Finset.univ = ∑ i, ∑ k, a i * star (a k) * T {i.castAdd n, k.natAdd n}

def IsometryInv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j j' : Fl g → Pt E g → ℂ)
    (h h' : Pt E g → ℝ) (φ : Pt E g → ℂ), IsDatum B τ M j h → IsDatum B τ M j' h' →
    IsBundleIso B τ M j j' φ → IsIsometry B h h' φ → ∀ (β : Fin n → E), ∀ b ∈ B, ∀ T,
      IsTorsionForm τ M j h β b T → IsTorsionForm τ M j' h' β b T

def TranslationInv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsDatum B τ M j h → ∀ (x : Fl g) (β : Fin n → E), ∀ b ∈ B, ∀ T,
      IsTorsionForm τ M j h β b T →
        IsTorsionForm τ M (translPullFactor τ x j) (fun P => h (transl τ x P)) β b T

def SymplecticInv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (γ : Sp g) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsPeriodMap B τ → IsDatum B (fun b => moeb γ (τ b)) (latAct M γ) j h →
    ∀ (β : Fin n → E), ∀ b ∈ B, ∀ T, IsTorsionForm (fun b => moeb γ (τ b)) (latAct M γ) j h β b T →
      IsTorsionForm τ M (fun l P => j (l ᵥ* (γ⁻¹).mat) (reframe τ γ P)) (fun P => h (reframe τ γ P))
        β b T

open Classical in

def twistFactor {E : Type} {g : ℕ} (M M' : Submodule ℤ (Fl g))
    (χ : AddChar (M' ⧸ M.submoduleOf M') ℂ) (j : Fl g → Pt E g → ℂ) (l : Fl g) (P : Pt E g) : ℂ :=
  if hl : l ∈ M' then χ (Submodule.Quotient.mk ⟨l, hl⟩) * j l P else 0

def CoverSum : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M M' : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsDatum B τ M' j h → IsLat M → M ≤ M' → ∀ (β : Fin n → E), ∀ b ∈ B,
    ∀ T : AddChar (M' ⧸ M.submoduleOf M') ℂ → Ext (n + n),
      (∀ χ, IsTorsionForm τ M' (twistFactor M M' χ j) h β b (T χ)) →
      IsTorsionForm τ M j h β b (∑ᶠ χ, T χ)

def FlatAcyclic : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsDatum B τ M j h → ChernIsFlat B τ h → ∀ b ∈ B, IsAcyclicAt τ M j h b

end GlobalTheory.TorsionForm
