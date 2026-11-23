import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentialEtaPeriod

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane

def principalForm (Λ : Submodule ℤ ℂ) (z w : ℂ) : ℂ :=
  z * starRingEnd ℂ w / (ZLattice.covolume Λ : ℝ)

def sqLen (Λ : Submodule ℤ ℂ) (z : ℂ) : ℝ := Real.pi * (principalForm Λ z z).re

def IsExponential {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (D : epsR R ⟶ A) (φ : R →+* ℂ)
    (ex : ℂ → (Over.mk (spMap φ) ⟶ A)) (Λ : Submodule ℤ ℂ) : Prop :=
  (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧ (∀ z, ex z = 1 ↔ z ∈ Λ) ∧
    DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set ℂ) = ⊤ ∧
    IsHolTo Set.univ (fun z => (ex z).left) ∧
    IsDerivAt0 (g := 1) (fun z => (ex (z 0)).left) (fun _ => 1)
      (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ) ≫ D.left)

def IsClassPoint {K : Type} [Field K] [NumberField K] (io : K →+* ℂ) (C : ClassGroup (𝓞 K)) (τ : ℍ) : Prop :=
  ∃ (I : nonZeroDivisors (Ideal (𝓞 K))) (ω : ℂ), ClassGroup.mk0 I = C ∧ ω ≠ 0 ∧
    ∀ z : ℂ, (∃ a ∈ (I : Ideal (𝓞 K)), io (a : K) = z) ↔ ∃ m n : ℤ, z = ω * (m + n * (τ : ℂ))

def etaPeriod (τ : ℍ) : ℝ := 4 * Real.pi * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4

def HasCMCurveOver {K : Type} [Field K] [NumberField K] (io : K →+* ℂ) (M : Type) [Field M] [NumberField M]
    (s₀ : M →+* ℂ) : Prop :=
  ∃ (j : 𝓞 K →+* 𝓞 M) (A : Over (Sp (𝓞 M))) (_ : GrpObj A) (act : OAct (𝓞 K) A) (D : epsR (𝓞 M) ⟶ A)
    (ex : ∀ s : M →+* ℂ, ℂ → (Over.mk (spMap (s.comp (algebraMap (𝓞 M) M))) ⟶ A))
    (Λ : (M →+* ℂ) → Submodule ℤ ℂ),
    (∀ a : 𝓞 K, s₀ (j a : M) = io (a : K)) ∧
    ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme A ∧
    IsLieBasis (fun _ : Fin 1 => D) ∧
    (∀ a : 𝓞 K, (D ≫ act.act a).left = spMap (epsScaleR (j a)) ≫ D.left) ∧
    (∀ s, IsExponential A D (s.comp (algebraMap (𝓞 M) M)) (ex s) (Λ s)) ∧
    (∀ (s : M →+* ℂ) (a : 𝓞 K) (z : ℂ), ex s (s (j a : M) * z) = ex s z ≫ act.act a) ∧
    (∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ, z ∈ Λ s₀ ↔ ∃ a : 𝓞 K, z = c * io (a : K)) ∧
    (∃ τ : ClassGroup (𝓞 K) → ℍ, ∀ C, IsClassPoint io C (τ C)) ∧
    ∀ τ : ClassGroup (𝓞 K) → ℍ, (∀ C, IsClassPoint io C (τ C)) →
      (∑ s : M →+* ℂ, Real.log (sqLen (Λ s) 1)) / (Module.finrank ℚ M : ℝ) =
        -((∑ C, Real.log (etaPeriod (τ C))) / (classNumber K : ℝ))

def HasCMCurve {K : Type} [Field K] [NumberField K] (io : K →+* ℂ) : Prop :=
  ∃ (M : Type) (_ : Field M) (_ : NumberField M) (s₀ : M →+* ℂ), HasCMCurveOver io M s₀

def CMCurveWithPeriod : Prop :=
  ∀ (d : ℕ), d.Prime → d % 16 = 7 → ∀ (K : Type) [Field K] [NumberField K] (rt : K),
    Module.finrank ℚ K = 2 → rt ^ 2 = -(d : K) → ∀ io : K →+* ℂ, HasCMCurve io

end GlobalTheory.IndefiniteRowSideFullHecke.ExponentialEtaPeriod
