import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

def latCombo {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    (b' : Module.Basis T ℤ (dualLattice F')) (c : T → ℤ) : Fin i → K :=
  ∑ t, c t • (b' t : Fin i → K)

def graphFirstForm {T : Type} [Fintype T] (c : T → ℤ) : MRing (stackedBlocks T) :=
  ∑ t, C (c t) * graphFirst t

def graphSecondForm {T : Type} [Fintype T] (d : T → ℤ) : MRing (stackedBlocks T) :=
  ∑ t, C (d t) * graphSecond t

def QuadIdentity {K : Type} [Field K] {i : ℕ} (φ₁ φ₂ φ₃ φ₄ : Fin i → K) : Prop :=
  ∀ x : Fin i → K, (φ₁ ⬝ᵥ x) * (φ₂ ⬝ᵥ x) = (φ₃ ⬝ᵥ x) * (φ₄ ⬝ᵥ x)

def excChartIdeal {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (u : T) :
    Ideal (MRing (stackedBlocks T)) :=
  stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u}

abbrev excChartRing {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (v u : T) : Type :=
  Localization.Away (Ideal.Quotient.mk (excChartIdeal b' a u) (graphFirst v * graphSecond u))

def excChartMap {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (v u : T) :
    MRing (stackedBlocks T) →+* excChartRing b' a v u :=
  (algebraMap (MRing (stackedBlocks T) ⧸ excChartIdeal b' a u) (excChartRing b' a v u)).comp
    (Ideal.Quotient.mk (excChartIdeal b' a u))

def DualStackedGraphQuadRel.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ),
    (∀ c₁ c₂ c₃ c₄ : T → ℤ,
      QuadIdentity (latCombo b' c₁) (latCombo b' c₂) (latCombo b' c₃) (latCombo b' c₄) →
      graphFirstForm c₁ * graphFirstForm c₂ - graphFirstForm c₃ * graphFirstForm c₄ ∈ stackedGraph b' a) ∧
    (∀ c₁ d₂ c₃ d₄ : T → ℤ,
      QuadIdentity (latCombo b' c₁) (latCombo b' fun t => d₂ t * a t) (latCombo b' c₃)
        (latCombo b' fun t => d₄ t * a t) →
      graphFirstForm c₁ * graphSecondForm d₂ - graphFirstForm c₃ * graphSecondForm d₄ ∈ stackedGraph b' a)

def DualStackedExcChartResidue.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      ∀ v u : T, ∃ σ₀ : k →+* excChartRing b' a v u, ∀ (ω : 𝓞 K) (c : T → ℤ),
        latCombo b' c = algebraMap (𝓞 K) K ω • (b' v : Fin i → K) →
        σ₀ (ρ ω) * excChartMap b' a v u (graphFirst v) = excChartMap b' a v u (graphFirstForm c)

def DualStackedExcChartForms.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      ∀ v u : T, ∃ σ₀ : k →+* excChartRing b' a v u,
        (∀ (ω : 𝓞 K) (c : T → ℤ), latCombo b' c = algebraMap (𝓞 K) K ω • (b' v : Fin i → K) →
          σ₀ (ρ ω) * excChartMap b' a v u (graphFirst v) = excChartMap b' a v u (graphFirstForm c)) ∧
        ∃ W : Fin (m + 1) → excChartRing b' a v u,
          ∀ t, ∑ j, σ₀ (M t j) * W j = excChartMap b' a v u (graphSecond t)

namespace DualStackedExcChartPartsExample

end DualStackedExcChartPartsExample

end

end GroundTheory.Heights₂.Heights
