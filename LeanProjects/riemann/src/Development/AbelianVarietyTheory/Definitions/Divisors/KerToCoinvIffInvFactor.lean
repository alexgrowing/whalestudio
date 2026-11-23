import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RallisCoinvariants
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DegeneratePrincipalSeriesUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantLinOm

noncomputable section

open GlobalTheory.WeilM GlobalTheory.LinPair
open scoped Matrix

namespace GlobalTheory.RallisSplit

def CoinvToKer : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m : ℕ) (JA : Matrix (Fin m) (Fin m) E), IsHerm c JA →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ))
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ), IsLinPair c ψ ξ JA JB co χ Cy om → IsYForm c ψ co Cy l →
    ∀ φ ∈ locAug om, secMap om l φ = 0

def KerToCoinv : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m : ℕ) (JA : Matrix (Fin m) (Fin m) E), IsHerm c JA →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ))
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ), IsLinPair c ψ ξ JA JB co χ Cy om → IsYForm c ψ co Cy l →
    ∀ φ ∈ SB (κ → k), secMap om l φ = 0 → φ ∈ locAug om

def InvFactor : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m : ℕ) (JA : Matrix (Fin m) (Fin m) E), IsHerm c JA →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ))
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ), IsLinPair c ψ ξ JA JB co χ Cy om → IsYForm c ψ co Cy l →
    ∀ T : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∀ z ∈ locAug om, T z = 0) → ∀ φ ∈ SB (κ → k), secMap om l φ = 0 → T φ = 0

def KSLow : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m : ℕ) (JA : Matrix (Fin m) (Fin m) E), IsHerm c JA →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ))
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ), IsLinPair c ψ ξ JA JB co χ Cy om → IsYForm c ψ co Cy l →
    m < n → secSpace om l ≠ ⊥ ∧ ∀ N : Submodule ℂ (UG c JB → ℂ), N ≤ secSpace om l →
      (∀ h : UG c JB, ∀ f ∈ N, (fun x => f (x * h)) ∈ N) → N = ⊥ ∨ N = secSpace om l

def KSHigh : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m : ℕ) (JA : Matrix (Fin m) (Fin m) E), IsHerm c JA →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ))
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ), IsLinPair c ψ ξ JA JB co χ Cy om → IsYForm c ψ co Cy l →
    n < m → ∀ (m' r : ℕ) (JA' : Matrix (Fin m') (Fin m') E), IsHerm c JA' → m + m' = 2 * n → IsWittStep c r JA JA' →
      ∀ (κ' : Type) [Fintype κ'] (co' : Darboux (symp c ξ JA' JB) κ')
        (om' : UG c JA' × UG c JB →* Module.End ℂ ((κ' → k) → ℂ)) (l' : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ),
        IsLinPair c ψ ξ JA' JB co' χ Cy om' → IsYForm c ψ co' Cy l' →
        ∃ q : secSpace om l →ₗ[ℂ] secSpace om' l', Function.Surjective q ∧
          ∀ (h : UG c JB) (f f₁ : secSpace om l), (∀ x, f₁.1 x = f.1 (x * h)) → ∀ x, (q f₁).1 x = (q f).1 (x * h)

theorem vanish_locAug_iff {G H Y : Type} [Group G] [Group H] [TopologicalSpace Y] (om : G × H →* Module.End ℂ (Y → ℂ))
    (T : (Y → ℂ) →ₗ[ℂ] ℂ) : (∀ z ∈ locAug om, T z = 0) ↔ ∀ g : G, ∀ φ ∈ SB Y, T (om (g, 1) φ) = T φ := by
  refine ⟨fun h g φ hφ => ?_, fun h z hz => ?_⟩
  · rw [← sub_eq_zero, ← map_sub]
    exact h _ (Submodule.subset_span ⟨g, φ, hφ, rfl⟩)
  · refine (Submodule.span_le (p := LinearMap.ker T)).2 ?_ hz
    rintro _ ⟨g, φ, hφ, rfl⟩
    exact LinearMap.mem_ker.2 (by rw [map_sub, h g φ hφ, sub_self])

theorem secSpace_ne_bot {G H Y : Type} [Group G] [Group H] [TopologicalSpace Y] (om : G × H →* Module.End ℂ (Y → ℂ))
    {l : (Y → ℂ) →ₗ[ℂ] ℂ} (hl : ∃ φ ∈ SB Y, l φ ≠ 0) : secSpace om l ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := hl
  intro e
  have h : secMap om l φ ∈ secSpace om l := ⟨φ, hφ, rfl⟩
  rw [e, Submodule.mem_bot] at h
  have := congrFun h 1
  rw [secMap_apply, show ((1 : G), (1 : H)) = 1 from rfl, map_one] at this
  exact h0 this

example (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E]
    (c : E →ₐ[k] E) (δ : E) (hq : IsQuad c δ) (ψ : AddChar k ℂ) (h1 : Continuous ψ) (h2 : ∀ t, ‖ψ t‖ = 1) (h3 : ψ ≠ 1) :
    ∃ (JA JB : Matrix (Fin 2) (Fin 2) E) (Cy : Matrix (Fin 2) (Fin 1) E) (co : Darboux (symp c 1 JA JB) (Fin 4))
      (om : UG c JA × UG c JB →* Module.End ℂ ((Fin 4 → k) → ℂ)) (l : ((Fin 4 → k) → ℂ) →ₗ[ℂ] ℂ),
      (∀ i j, c (1 * JB j i) = -(1 * JB i j)) ∧ JB.det ≠ 0 ∧ IsHerm c JA ∧ ResEtaPow (R := k) ⊥ (1 : Eˣ →* Circle) 2 ∧
      IsLinPair c ψ 1 JA JB co 1 Cy om ∧ IsYForm c ψ co Cy l ∧ (∀ z ∈ locAug om, l z = 0) ∧ secSpace om l ≠ ⊥ := by
  obtain ⟨Cy, co, om, l, h, hl⟩ := GlobalTheory.HypPair.exists_linPair k E c δ hq ψ h1 h2 h3
  exact ⟨_, _, Cy, co, om, l, fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp,
    ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp⟩, fun a => by simp, h, hl,
    (vanish_locAug_iff om l).2 (h.lin l hl.1), secSpace_ne_bot om hl.2⟩

example {G H Y : Type} [Group G] [Group H] [TopologicalSpace Y] : locAug (1 : G × H →* Module.End ℂ (Y → ℂ)) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨g, φ, -, rfl⟩
  simp

example {G H Y : Type} [Group G] [Group H] (l : (Y → ℂ) →ₗ[ℂ] ℂ) (φ : Y → ℂ) :
    secMap (1 : G × H →* Module.End ℂ (Y → ℂ)) l φ = fun _ => l φ := rfl

end GlobalTheory.RallisSplit

end
