import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.Imports

set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

def LatticeCommensurable : Prop :=
  ∀ (I : AutInst) (x : I.GA), ∃ m : ℕ, 1 ≤ m ∧
    (∀ u ∈ latSet I x, (m : I.E) • u ∈ I.L) ∧ ∀ u ∈ I.L, (m : I.E) • u ∈ latSet I x

def LatticeFinitelyGenerated : Prop :=
  ∀ (I : AutInst) (x : I.GA), ∃ M : Submodule (𝓞 I.E) (Fin I.n → I.E),
    M.FG ∧ (M : Set (Fin I.n → I.E)) = latSet I x

def ExistsBoundedBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n j : ℕ) (M B : Submodule (𝓞 K) (Fin n → K))
    (b : Fin j → Fin n → K), M.FG → B ≤ M → LinearIndependent K b → (∀ a, b a ∈ B) →
    (B : Set (Fin n → K)) ⊆ Submodule.span K (Set.range b) →
    Finite (B ⧸ (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype)

def SubmoduleExists : Prop :=
  ∀ I : AutInst, 1 ≤ I.n → ∀ x : I.GA, Nonempty (Sub I x)

def LatticeRightInvariant : Prop :=
  ∀ (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf), k ∈ I.Kset → latSet I (x * (y, k)) = latSet I x

def GramDistortionBound : Prop :=
  ∀ (n j : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin j) ℂ) (a b : ℝ), 0 ≤ a →
    (∀ w : Fin n → ℂ, a * ∑ i, ‖w i‖ ^ 2 ≤ ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ∧
      ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤ b * ∑ i, ‖w i‖ ^ 2) →
    a ^ j * (Cᴴ * C).det.re ≤ ((Y * C)ᴴ * (Y * C)).det.re ∧
      ((Y * C)ᴴ * (Y * C)).det.re ≤ b ^ j * (Cᴴ * C).det.re

def SizesLocallyComparable : Prop :=
  ∀ (I : AutInst) (x : I.GA) (r : ℝ), 1 < r → ∀ᶠ x' in 𝓝 x,
    (∀ s : Sub I x, ∃ s' : Sub I x', size I s' ≤ r * size I s) ∧
      ∀ s' : Sub I x', ∃ s : Sub I x, size I s ≤ r * size I s'

def InfimumContinuousFamily : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (S : X → Type) (g : ∀ x, S x → ℝ),
    (∀ x, Nonempty (S x)) → (∀ x s, 0 ≤ g x s) →
    (∀ x (r : ℝ), 1 < r → ∀ᶠ x' in 𝓝 x,
      (∀ s, ∃ s', g x' s' ≤ r * g x s) ∧ ∀ s', ∃ s, g x s ≤ r * g x' s') →
    Continuous fun x => min (1 / 2 : ℝ) (⨅ s, g x s)

def MinkowskiFirstTheorem : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L],
      ∃ u ∈ L, u ≠ 0 ∧ ‖u‖ ^ 2 ≤ C * ZLattice.covolume L ^ ((2 : ℝ) / d)

def MinkowskiSubmodule : Prop :=
  ∀ I : AutInst, ∃ c : ℝ, 0 < c ∧ ∀ (x : I.GA) (s : Sub I x), ∃ u ∈ s.B, u ≠ 0 ∧
    ∑ v, ∑ i, ‖coordV I x v u i‖ ^ 2 ≤ c * size I s ^ 2

def LatticeVectorsBoundedBelow : Prop :=
  ∀ (I : AutInst) (x : I.GA), ∃ l : ℝ, 0 < l ∧ ∀ u ∈ latSet I x, u ≠ 0 →
    l ≤ ∑ v, ∑ i, ‖coordV I x v u i‖ ^ 2

def HeightsPositive : Prop :=
  ∀ (I : AutInst) (x : I.GA) (s : Sub I x), 0 < ht I s

end Formalism.L2.SG.Pf.Tau
