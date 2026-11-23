import Formalism.LatticeTheta.Statement

open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def LatticeSummableDecay [FiniteDimensional ℝ V] : Prop :=
  ∀ (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (g : V → ℂ) (b : ℝ),
    (Module.finrank ℝ V : ℝ) < b → g =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    Summable (fun l : L => g l)

def Periodization [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ), Continuous f →
    ∀ b : ℝ, (Module.finrank ℝ V : ℝ) < b → f =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    Integrable f ∧ (∀ x : V, Summable (fun l : Λ => f ((l : V) + x))) ∧
    Continuous (fun x : V => ∑' l : Λ, f ((l : V) + x)) ∧
    ∀ (l₀ : Λ) (x : V), ∑' l : Λ, f ((l : V) + ((l₀ : V) + x)) = ∑' l : Λ, f ((l : V) + x)

def UnfoldCoeff [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ), Integrable f →
    ∀ D : Set V, IsAddFundamentalDomain Λ D volume → ∀ μ ∈ dual Λ,
      ∫ y in D, (∑' l : Λ, f ((l : V) + y)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ

def LatticeFourierSeries [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (G : V → ℂ), Continuous G →
    (∀ (l : Λ) (x : V), G ((l : V) + x) = G x) →
    ∀ D : Set V, IsAddFundamentalDomain Λ D volume →
    Summable (fun μ : dual Λ =>
      ∫ y in D, G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ)))) →
    ∀ x : V, HasSum (fun μ : dual Λ =>
        (ZLattice.covolume Λ : ℂ)⁻¹ *
          (∫ y in D, G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ)))) *
          Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))
      (G x)

def GaussFourier [FiniteDimensional ℝ V] : Prop :=
  ∀ t : ℝ, 0 < t →
    Continuous (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) ∧
    (∀ b : ℝ, (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) =O[cocompact V]
      (fun v => ‖v‖ ^ (-b))) ∧
    ∀ w : V, (𝓕 (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) : V → ℂ) w =
      ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) * (Real.exp (-Real.pi * ‖w‖ ^ 2 / t) : ℂ)

def SchwartzDecay [FiniteDimensional ℝ V] : Prop :=
  ∀ (f : 𝓢(V, ℂ)) (b : ℝ),
    (f : V → ℂ) =O[cocompact V] (fun v => ‖v‖ ^ (-b)) ∧
    (𝓕 (f : V → ℂ) : V → ℂ) =O[cocompact V] (fun v => ‖v‖ ^ (-b))

end Formalism.H
