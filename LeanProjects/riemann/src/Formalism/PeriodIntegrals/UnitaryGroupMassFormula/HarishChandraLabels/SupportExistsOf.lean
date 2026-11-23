import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.GreenHCLabelOf

open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
open scoped TensorProduct
namespace PI.GreenHCLabel

def SimpleIrr : Prop :=
  ∀ (Γ : Type) [Group Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrrRep τ.ρ

def ConstSymm : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V), Simple τ → (IsConstituent τ ρ ↔ ∃ ψ ∈ Intw ρ τ.ρ, ψ ≠ 0)

def CommonConst : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ V'),
    Simple τ → IsConstituent τ ρ → IsConstituent τ ρ' → ∃ φ ∈ Intw ρ ρ', φ ≠ 0

def ProdSimple : Prop :=
  ∀ (s : ℕ) (L : Fin s → Type) [∀ c, Group (L c)] [∀ c, Fintype (L c)] (W : Type) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Nontrivial W] (ρ : Representation ℂ (∀ c, L c) W),
    ∃ (lam : ∀ c, FDRep ℂ (L c)) (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] W), (∀ c, Simple (lam c)) ∧ Φ ≠ 0 ∧
      ∀ g : ∀ c, L c, Φ ∘ₗ PiTensorProduct.map (fun c => (lam c).ρ (g c)) = ρ g ∘ₗ Φ

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def Frob : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (τ : FDRep ℂ (GL ι K)) (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ), Φ ≠ 0 →
    (∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) → ∃ ψ ∈ Intw (hcRep K b lam) τ.ρ, ψ ≠ 0

def HCFin : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    FiniteDimensional ℂ (hcSpace K b lam)

def Jacquet : Prop :=
  ∀ (n : ℕ) (τ : FDRep ℂ (GL (Fin n) K)), Simple τ →
    ∃ (s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
      (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ),
      Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧ Φ ≠ 0 ∧
      ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ

variable {K}

theorem supportExists_of (h1 : Jacquet K) (h2 : Frob K) (h3 : HCFin K) (h4 : ConstSymm) : SupportExists K := by
  intro n τ hτ
  obtain ⟨s, b, lam, Φ, hb, hlam, hΦ, hpar⟩ := h1 n τ hτ
  obtain ⟨ψ, hψ, hψ0⟩ := h2 (Fin n) s b lam τ Φ hΦ hpar
  refine ⟨s, b, lam, hb, hlam, ?_⟩
  haveI := h3 (Fin n) s b lam
  exact (h4 (GL (Fin n) K) τ (hcSpace K b lam) (hcRep K b lam) hτ).mpr ⟨ψ, hψ, hψ0⟩

end PI.GreenHCLabel
