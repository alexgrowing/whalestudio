import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors

def ContainsData (D : D7) (M : IntermediateField ℚ ℂ) (Λ : AddSubgroup ℂ) : Prop :=
  (∀ x : D.host.K, D.host.φ₀ (x : D.host.E) ∈ M) ∧ g2 Λ ∈ M ∧ g3 Λ ∈ M

def FixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Prop :=
  ∀ (x : D.host.K) (y : M), (y : ℂ) = D.host.φ₀ (x : D.host.E) → ρ y = (y : ℂ)

def conjEmb (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : M →ₐ[ℚ] ℂ :=
  ((Complex.conjAe : ℂ →ₐ[ℝ] ℂ).restrictScalars ℚ).comp ρ

def HomotheticTo (D : D7) (Λ' : AddSubgroup ℂ) (c' : Ideal (𝓞 D.host.K)) : Prop :=
  ∃ x : ℂ, x ≠ 0 ∧ Λ' = lamOf D c' x

def normArea (D : D7) (c' : Ideal (𝓞 D.host.K)) : ℝ :=
  ‖Formalism.MainNotions.TaylorLogMetric.discr (lamOf D c' 1)‖ ^ ((1 : ℝ) / 6) * area (lamOf D c' 1)

def ConjugatesEquidistributed : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
  ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], ContainsData D M (lamOf D cc δ) →
    (∃ c : {ρ : M →ₐ[ℚ] ℂ // FixesK D M ρ} → (Ideal (𝓞 D.host.K))⁰,
      (∀ ρ, HomotheticTo D (lamConj M ρ.1 (lamOf D cc δ)) (c ρ : Ideal (𝓞 D.host.K))) ∧
      ∀ C C' : ClassGroup (𝓞 D.host.K),
        Nat.card {ρ // ClassGroup.mk0 (c ρ) = C} = Nat.card {ρ // ClassGroup.mk0 (c ρ) = C'}) ∧
    (∀ ρ : M →ₐ[ℚ] ℂ, ¬ FixesK D M ρ →
      FixesK D M (conjEmb M ρ) ∧
      area (lamConj M ρ (lamOf D cc δ)) = area (lamConj M (conjEmb M ρ) (lamOf D cc δ))) ∧
    (∀ r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰, (∀ C, ClassGroup.mk0 (r C) = C) →
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) =
        (∑ C : ClassGroup (𝓞 D.host.K), Real.log (normArea D (r C : Ideal (𝓞 D.host.K)))) /
          (classNumber D.host.K : ℝ))

theorem conjEmb_apply (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (y : M) :
    conjEmb M ρ y = (starRingEnd ℂ) (ρ y) := rfl

theorem exists_representatives (D : D7) :
    ∃ r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰, ∀ C, ClassGroup.mk0 (r C) = C :=
  ⟨Function.surjInv ClassGroup.mk0_surjective, Function.surjInv_eq _⟩

end GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates
