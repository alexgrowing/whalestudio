import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerToCoinvIffInvFactor

noncomputable section

open GlobalTheory.WeilM GlobalTheory.LinPair
open scoped Matrix

namespace GlobalTheory.KSTransfer

def colX {E : Type} {m m' r : ℕ} (P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) : Matrix (Fin m) (Fin r) E :=
  P.submatrix id (fun i => Sum.inr (Sum.inl i))

def colA {E : Type} {m m' r : ℕ} (P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) : Matrix (Fin m) (Fin m') E :=
  P.submatrix id Sum.inl

def detMod (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] {E : Type} [Field E]
    [Algebra k E] {r : ℕ} (a : GL (Fin r) E) : ℝ :=
  ((sbClass k).modu (Units.map (Algebra.norm k : E →* k) (Matrix.GeneralLinearGroup.det a)) : ℝ)

def IsJacq {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] (c : E →ₐ[k] E)
    (ψ : AddChar k ℂ) {ξ : E} {m m' r d : ℕ} {JA : Matrix (Fin m) (Fin m) E} {JA' : Matrix (Fin m') (Fin m') E}
    {JB : Matrix (Fin d) (Fin d) E} {κ κ' : Type} [Fintype κ] [Fintype κ'] [TopologicalSpace k]
    (co : Darboux (symp c ξ JA JB) κ) (co' : Darboux (symp c ξ JA' JB) κ')
    (P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) (J : ((κ → k) → ℂ) →ₗ[ℂ] ((κ' → k) → ℂ)) : Prop :=
  (∀ φ ∈ SB (κ → k), J φ ∈ SB (κ' → k)) ∧
  (∀ z : Matrix (Fin r) (Fin d) E, ∀ φ ∈ SB (κ → k), J (co.rho ψ (colX P * z) φ) = J φ) ∧
  (∀ w : Matrix (Fin m') (Fin d) E, ∀ φ ∈ SB (κ → k), J (co.rho ψ (colA P * w) φ) = co'.rho ψ w (J φ)) ∧
  ∃ φ ∈ SB (κ → k), J φ ≠ 0

def JacqExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m m' r : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JA' : Matrix (Fin m') (Fin m') E), IsHerm c JA → IsHerm c JA' →
  ∀ P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E, m = m' + 2 * r → 0 < r →
    Pᵀ * JA * P.map c = (Matrix.fromBlocks JA' 0 0 (Matrix.fromBlocks 0 1 1 0) :
      Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (κ' : Type) [Fintype κ'] (co' : Darboux (symp c ξ JA' JB) κ'),
    ∃ J : ((κ → k) → ℂ) →ₗ[ℂ] ((κ' → k) → ℂ), IsJacq c ψ co co' P J

def JacqEquivB : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m m' r : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JA' : Matrix (Fin m') (Fin m') E), IsHerm c JA → IsHerm c JA' →
  ∀ P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E, m = m' + 2 * r → 0 < r →
    Pᵀ * JA * P.map c = (Matrix.fromBlocks JA' 0 0 (Matrix.fromBlocks 0 1 1 0) :
      Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)),
    IsLinPair c ψ ξ JA JB co χ Cy om → n < m → m + m' = 2 * n →
  ∀ (κ' : Type) [Fintype κ'] (co' : Darboux (symp c ξ JA' JB) κ')
    (om' : UG c JA' × UG c JB →* Module.End ℂ ((κ' → k) → ℂ)) (l' : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ),
    IsLinPair c ψ ξ JA' JB co' χ Cy om' → IsYForm c ψ co' Cy l' →
  ∀ J : ((κ → k) → ℂ) →ₗ[ℂ] ((κ' → k) → ℂ), IsJacq c ψ co co' P J →
    ∀ h : UG c JB, ∀ φ ∈ SB (κ → k), secMap om' l' (J (om (1, h) φ)) = secMap om' l' (om' (1, h) (J φ))

def JacqCovQ : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m m' r : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JA' : Matrix (Fin m') (Fin m') E), IsHerm c JA → IsHerm c JA' →
  ∀ P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E, m = m' + 2 * r → 0 < r →
    Pᵀ * JA * P.map c = (Matrix.fromBlocks JA' 0 0 (Matrix.fromBlocks 0 1 1 0) :
      Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)),
    IsLinPair c ψ ξ JA JB co χ Cy om → n < m → m + m' = 2 * n →
  ∀ (κ' : Type) [Fintype κ'] (co' : Darboux (symp c ξ JA' JB) κ')
    (om' : UG c JA' × UG c JB →* Module.End ℂ ((κ' → k) → ℂ)) (l' : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ),
    IsLinPair c ψ ξ JA' JB co' χ Cy om' → IsYForm c ψ co' Cy l' →
  ∀ J : ((κ → k) → ℂ) →ₗ[ℂ] ((κ' → k) → ℂ), IsJacq c ψ co co' P J →
    ∀ (q : UG c JA) (a : GL (Fin r) E), ((q : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) * colX P = colX P * (a : Matrix (Fin r) (Fin r) E) →
      ∀ φ ∈ SB (κ → k), secMap om' l' (J (om (q, 1) φ)) = ((detMod k a ^ n : ℝ) : ℂ) • secMap om' l' (J φ)

def JacqPos : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m m' r : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JA' : Matrix (Fin m') (Fin m') E), IsHerm c JA → IsHerm c JA' →
  ∀ P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E, m = m' + 2 * r → 0 < r →
    Pᵀ * JA * P.map c = (Matrix.fromBlocks JA' 0 0 (Matrix.fromBlocks 0 1 1 0) :
      Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)),
    IsLinPair c ψ ξ JA JB co χ Cy om → n < m → m + m' = 2 * n →
  ∀ (κ' : Type) [Fintype κ'] (co' : Darboux (symp c ξ JA' JB) κ')
    (om' : UG c JA' × UG c JB →* Module.End ℂ ((κ' → k) → ℂ)) (l' : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ),
    IsLinPair c ψ ξ JA' JB co' χ Cy om' → IsYForm c ψ co' Cy l' →
  ∀ J : ((κ → k) → ℂ) →ₗ[ℂ] ((κ' → k) → ℂ), IsJacq c ψ co co' P J →
    ∃ φ ∈ SB (κ → k), ∃ c₀ : ℂ, (∀ g : UG c JA, ∃ t : ℝ, 0 ≤ t ∧ l' (J (om (g, 1) φ)) = c₀ * t) ∧ l' (J φ) ≠ 0

def SmoothA : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m : ℕ) (JA : Matrix (Fin m) (Fin m) E), IsHerm c JA →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)),
    IsLinPair c ψ ξ JA JB co χ Cy om →
    ∀ φ ∈ SB (κ → k), ∃ U : Subgroup (UG c JA), IsOpen (U : Set (UG c JA)) ∧ ∀ u ∈ U, om (u, 1) φ = φ

def AvgExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ (m m' r : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JA' : Matrix (Fin m') (Fin m') E), IsHerm c JA → IsHerm c JA' →
  ∀ P : Matrix (Fin m) (Fin m' ⊕ (Fin r ⊕ Fin r)) E, m = m' + 2 * r → 0 < r →
    Pᵀ * JA * P.map c = (Matrix.fromBlocks JA' 0 0 (Matrix.fromBlocks 0 1 1 0) :
      Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E) →
    ∃ Av : (UG c JA → ℂ) →ₗ[ℂ] ℂ,
      (∀ U : Subgroup (UG c JA), IsOpen (U : Set (UG c JA)) → ∃ (s : Finset (UG c JA)) (w : UG c JA → ℂ),
        ∀ F : UG c JA → ℂ, (∀ g, ∀ u ∈ U, F (g * u) = F g) → Av F = ∑ g ∈ s, w g * F g) ∧
      (∀ F : UG c JA → ℂ, (∃ U : Subgroup (UG c JA), IsOpen (U : Set (UG c JA)) ∧ ∀ g, ∀ u ∈ U, F (g * u) = F g) →
        (∀ (q : UG c JA) (a : GL (Fin r) E),
          ((q : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) * colX P = colX P * (a : Matrix (Fin r) (Fin r) E) →
          ∀ g, F (q * g) = ((detMod k a ^ (m' + r) : ℝ) : ℂ) * F g) →
        ∀ g₀, Av (fun g => F (g * g₀)) = Av F) ∧
      (∀ F : UG c JA → ℂ, (∃ U : Subgroup (UG c JA), IsOpen (U : Set (UG c JA)) ∧ ∀ g, ∀ u ∈ U, F (g * u) = F g) →
        (∀ g, ∃ t : ℝ, 0 ≤ t ∧ F g = t) → F 1 ≠ 0 → Av F ≠ 0)

end GlobalTheory.KSTransfer

end
