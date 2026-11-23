import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingEqZeroIff
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
open Pointwise in

theorem _root_.GlobalTheory.finite_quotSMulTop_X_sub_one_of_chart : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [_root_.GlobalTheory.PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢] (i : ι) (B : Type) (_ : CommRing B) (_ : Algebra R B)
    (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
    (ε : G →ₛₗ[(π : MvPolynomial ι R →+* B)] P),
    (Function.Surjective π ∧ π (MvPolynomial.X i) = 1 ∧ Function.Surjective ε ∧
      ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) →
    (Module.Finite B P → Module.Finite (MvPolynomial ι R)
      (QuotSMulTop ((MvPolynomial.X i : MvPolynomial ι R) - 1) G)) ∧
    (Algebra.FinitePresentation R B → Module.FinitePresentation B P →
      Module.FinitePresentation (MvPolynomial ι R)
        (QuotSMulTop ((MvPolynomial.X i : MvPolynomial ι R) - 1) G)) := by
  intro ι _ _ R _ G _ _ _ _ 𝒢 _ _ i B _ _ π P _ _ ε ⟨hπs, hπX, hεs, hker⟩
  letI : Algebra (MvPolynomial ι R) B := (π : MvPolynomial ι R →+* B).toAlgebra
  letI : Module (MvPolynomial ι R) P := Module.compHom P (π : MvPolynomial ι R →+* B)
  haveI : IsScalarTower (MvPolynomial ι R) B P :=
    ⟨fun a b p => by
      change (π a * b) • p = π a • b • p
      exact mul_smul _ _ _⟩
  have hkerε : ∀ y, ε y = 0 ↔ ∃ w : G, y = (MvPolynomial.X i - 1 : MvPolynomial ι R) • w :=
    _root_.GlobalTheory.dehomogenising_eq_zero_iff ι R G 𝒢 i B (π : MvPolynomial ι R →+* B) P ε hπX hker
  let ε' : G →ₗ[MvPolynomial ι R] P :=
    { toFun := ε
      map_add' := ε.map_add
      map_smul' := fun a g => ε.map_smulₛₗ a g }
  have hle : ((MvPolynomial.X i : MvPolynomial ι R) - 1) • (⊤ : Submodule (MvPolynomial ι R) G) ≤
      LinearMap.ker ε' := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact (hkerε _).2 ⟨y, rfl⟩
  let φ := Submodule.liftQ _ ε' hle
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.ker_liftQ_eq_bot
    intro x hx
    obtain ⟨w, rfl⟩ := (hkerε x).1 hx
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨w, trivial, rfl⟩
  have hsurj : Function.Surjective φ := by
    intro p
    obtain ⟨g, rfl⟩ := hεs p
    exact ⟨Submodule.Quotient.mk g, rfl⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  haveI : Module.Finite (MvPolynomial ι R) B :=
    Module.Finite.of_surjective (Algebra.linearMap (MvPolynomial ι R) B) hπs
  refine ⟨fun hP => ?_, fun hB hPfp => ?_⟩
  · haveI : Module.Finite (MvPolynomial ι R) P := Module.Finite.trans B P
    exact Module.Finite.equiv e.symm
  · haveI : IsScalarTower R (MvPolynomial ι R) B :=
      IsScalarTower.of_algebraMap_eq (fun r => (π.commutes r).symm)
    haveI : Algebra.FinitePresentation (MvPolynomial ι R) B :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) B
    haveI : Module.FinitePresentation (MvPolynomial ι R) B :=
      Module.FinitePresentation.of_finite_of_finitePresentation _ _
    haveI : Module.FinitePresentation (MvPolynomial ι R) P :=
      Module.FinitePresentation.trans (MvPolynomial ι R) P B
    exact Module.finitePresentation_of_surjective e.symm.toLinearMap e.symm.surjective
      (by rw [LinearEquiv.ker]; exact Submodule.fg_bot)

end GlobalTheory
