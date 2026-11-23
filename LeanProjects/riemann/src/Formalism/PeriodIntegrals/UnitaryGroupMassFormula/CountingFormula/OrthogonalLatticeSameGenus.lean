import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.MassConstUniqueOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsClassReps

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

section Glue

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]

def wPerp (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : Submodule K V1 := LinearMap.ker (h1 z)

def hPerp (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : wPerp h1 z →ₗ⋆[K] wPerp h1 z →ₗ[K] K :=
  (h1.compl₂ (wPerp h1 z).subtype).comp (wPerp h1 z).subtype

def l0 (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Submodule (𝓞 K) (wPerp h1 z) :=
  M.comap ((wPerp h1 z).subtype.restrictScalars (𝓞 K))

def IsGlueLat (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Prop :=
  Submodule.IsLattice K M ∧ Formalism.HermitianLatticesTheory.IsUnimodular h1 M ∧ z ∈ M ∧
    ∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c

def hz (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : Set (V1 ≃ₗ[K] V1) :=
  {σ | σ ∈ Formalism.HermitianLatticesTheory.isom h1 ∧ σ z = z}

def stabZ (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Set (V1 ≃ₗ[K] V1) :=
  {σ | σ ∈ hz h1 z ∧ Formalism.HermitianLatticesTheory.gmap σ M = M}

def IsHzReps (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (s : Finset (Submodule (𝓞 K) V1)) : Prop :=
  (∀ M ∈ s, IsGlueLat h1 z M) ∧
    ∀ M, IsGlueLat h1 z M → ∃! M', M' ∈ s ∧ ∃ σ ∈ hz h1 z, Formalism.HermitianLatticesTheory.gmap σ M' = M

def glueOf (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (L : Submodule (𝓞 K) (wPerp h1 z)) :
    Set (Submodule (𝓞 K) V1) :=
  {M | IsGlueLat h1 z M ∧ l0 h1 z M = L}

end Glue

def GlueHyp (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]
    (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ) : Prop :=
  Formalism.HermitianLatticesTheory.IsCMUnram K ∧ IsFixF K F ∧ h1.IsSymm ∧ h1 z z = -((t : ℕ) : K) ∧ 0 < t ∧
    IsTotPosDef (hPerp h1 z)

def OrthogonalLatticeSameGenus : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (V1 : Type) [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
    [IsScalarTower (𝓞 K) K V1] (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ),
    GlueHyp K F h1 z t → ∀ M M' : Submodule (𝓞 K) V1, IsGlueLat h1 z M → IsGlueLat h1 z M' →
      l0 h1 z M' ∈ Formalism.HermitianLatticesTheory.genus (hPerp h1 z) (l0 h1 z M)

def OrbitSum : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (V1 : Type) [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
    [IsScalarTower (𝓞 K) K V1] (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ),
    GlueHyp K F h1 z t → ∀ M₀ : Submodule (𝓞 K) V1, IsGlueLat h1 z M₀ →
      (∀ M, IsGlueLat h1 z M → l0 h1 z M ∈ Formalism.HermitianLatticesTheory.genus (hPerp h1 z) (l0 h1 z M₀)) →
      (∀ L ∈ Formalism.HermitianLatticesTheory.genus (hPerp h1 z) (l0 h1 z M₀), (glueOf h1 z L).Finite) →
      ∀ s, IsHzReps h1 z s → ∀ c, Formalism.ThetaLiftIndependence.IsClassReps (hPerp h1 z) (l0 h1 z M₀) c →
        ∑ M ∈ s, ((Nat.card (stabZ h1 z M) : ℝ))⁻¹ =
          ∑ L ∈ c, (Nat.card (glueOf h1 z L) : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL (hPerp h1 z) L) : ℝ)

def GlueCard : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (V1 : Type) [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
    [IsScalarTower (𝓞 K) K V1] (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ),
    GlueHyp K F h1 z t → ∀ M₀ : Submodule (𝓞 K) V1, IsGlueLat h1 z M₀ →
      ∀ L ∈ Formalism.HermitianLatticesTheory.genus (hPerp h1 z) (l0 h1 z M₀), (Nat.card (glueOf h1 z L) : ℝ) = glueT K F t

def LamOff : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (V1 : Type) [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
    [IsScalarTower (𝓞 K) K V1] (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ),
    GlueHyp K F h1 z t → ∀ M : Submodule (𝓞 K) V1, IsGlueLat h1 z M →
      ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ((t : ℕ) : 𝓞 F) ∉ 𝔭 → lamP (hPerp h1 z) (l0 h1 z M) 𝔭 = 1

def LamAt : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (V1 : Type) [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
    [IsScalarTower (𝓞 K) K V1] (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ),
    GlueHyp K F h1 z t → ∀ M : Submodule (𝓞 K) V1, IsGlueLat h1 z M →
      ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ((t : ℕ) : 𝓞 F) ∈ 𝔭 →
        lamP (hPerp h1 z) (l0 h1 z M) 𝔭 =
          (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K (wPerp h1 z) - 1) * vT F t 𝔭) *
            (1 - etaF K F 𝔭 ^ finrank K (wPerp h1 z) *
              (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K (wPerp h1 z) : ℤ))) /
            (1 - etaF K F 𝔭 * (Ideal.absNorm 𝔭 : ℝ)⁻¹)

def OrthogonalLatticeIntegral : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (V1 : Type) [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
    [IsScalarTower (𝓞 K) K V1] (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ),
    GlueHyp K F h1 z t → ∀ M : Submodule (𝓞 K) V1, IsGlueLat h1 z M →
      Submodule.IsLattice K (l0 h1 z M) ∧ Formalism.HermitianLatticesTheory.IsIntegralLat (hPerp h1 z) (l0 h1 z M)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

example {K : Type} [Field K] [StarRing K] {V1 : Type} [AddCommGroup V1] [Module K V1] (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (x y : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.wPerp h1 z) : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hPerp h1 z x y = h1 x y := rfl
