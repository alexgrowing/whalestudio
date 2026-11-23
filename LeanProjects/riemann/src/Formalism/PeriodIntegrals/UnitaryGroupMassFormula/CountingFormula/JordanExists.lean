import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowers

open NumberField Module IsDedekindDomain Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

def JordanExists : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → Module.finrank F K = 2 → h.IsSymm →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    Formalism.HermitianLatticesTheory.IsIntegralLat h (pbLat x 𝔞) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ b a, IsJordanIn h X (pbLat x 𝔞) 𝔭 b a

def DetLocal : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K), IsFixF K F →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    ∀ (𝔭 : Ideal (𝓞 F)) (b : Fin (finrank K X) → V) (a : Fin (finrank K X) → 𝓞 F), 𝔭.IsMaximal →
      IsJordanIn h X (pbLat x 𝔞) 𝔭 b a →
      ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          FractionalIdeal.count K P
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (∏ j, ((a j : 𝓞 F) : F))))

def CountExt : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K] (n : ℕ)
    (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)) (α : Fin n → 𝓞 F), 𝔭.IsMaximal →
    P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 → (∀ j, α j ≠ 0) →
    FractionalIdeal.count K P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (∏ j, ((α j : 𝓞 F) : F)))) =
      ((P.asIdeal.ramificationIdx (𝓞 F) * ∑ j, vF 𝔭 (α j) : ℕ) : ℤ)

def NormAssembly : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K],
    Module.finrank F K = 2 →
    ∀ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (w : Ideal (𝓞 F) → ℕ), J ≠ 0 →
    (∀ (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)), 𝔭.IsMaximal →
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P J = ((P.asIdeal.ramificationIdx (𝓞 F) * w 𝔭 : ℕ) : ℤ)) →
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ w 𝔭.1) ^ 2 =
      (FractionalIdeal.absNorm J : ℝ)

end PI.UnitaryGroupMassFormula.CntFormula.R6
