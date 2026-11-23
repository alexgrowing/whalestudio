import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ReducedTensors
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace NumberField TensorProduct
  GroundTheory.Arith.SchemeCoh ComplexAt

universe u

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ} (X : ProjScheme A N)

def baseHomOn (U : X.X.Opens) : A →+* Γ(X.X, U) :=
  (X.X.presheaf.map (homOfLE le_top).op).hom.comp
    ((X.toBase.appTop).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)

end ProjScheme

namespace SectionsLattice

open ProjScheme

def ValuesTorsion.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (X : ProjScheme (𝓞 K) N), IsReduced X.X →
    ∀ L : X.X.Modules, IsInvertibleSheaf L →
      ∀ (σ : K →+* ℂ) (ι : Type) [Fintype ι] (z : ι → ComplexAt σ), LinearIndependent (𝓞 K) z →
        ∀ s : ι → X.H0 L,
          (∀ x : X.complexPoints (intEmb σ),
              ∑ i, (ofComplex σ).symm (z i) • X.evalGlobalSection L x (s i) = 0) →
            ∀ i, ∃ d : 𝓞 K, d ≠ 0 ∧ d • s i = 0

def AffineNull.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (B : Type) [CommRing B] [Algebra (𝓞 K) B],
    Algebra.FiniteType (𝓞 K) B → IsReduced B →
      ∀ (ι : Type) [Fintype ι] (z : ι → ComplexAt σ), LinearIndependent (𝓞 K) z →
        ∀ f : ι → B,
          (∀ φ : B →+* ℂ, φ.comp (algebraMap (𝓞 K) B) = intEmb σ →
              ∑ i, (ofComplex σ).symm (z i) * φ (f i) = 0) →
            ∀ i, ∃ d : 𝓞 K, d ≠ 0 ∧ d • f i = 0

def ChartPoints.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N : ℕ) (X : ProjScheme A N) (ρ : A →+* ℂ) (W : X.X.Opens) (p : X.X),
    p ∈ W → ∃ U : X.X.Opens, p ∈ U ∧ U ≤ W ∧ (X.baseHomOn U).FiniteType ∧
      ∀ φ : Γ(X.X, U) →+* ℂ, φ.comp (X.baseHomOn U) = ρ →
        ∃ (x : X.complexPoints ρ) (hx : X.point x ∈ U), ∀ f : Γ(X.X, U),
          X.evalAtPoint x (germR hx f) = φ f

def LocalTorsion.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (X : ProjScheme (𝓞 K) N) (L : X.X.Modules)
    (s : X.H0 L),
    (∀ p : X.X, ∃ U : X.X.Opens, p ∈ U ∧ ∃ d : 𝓞 K, d ≠ 0 ∧
        resM ((preMod X.X).obj L) (le_top : U ≤ ⊤) (d • s) = 0) →
      ∃ d : 𝓞 K, d ≠ 0 ∧ d • s = 0

end SectionsLattice

namespace ProjScheme

theorem complexAt_smul_eq_zero {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {a : 𝓞 K}
    (ha : a ≠ 0) {z : ComplexAt σ} (h : a • z = 0) : z = 0 := by
  rw [ComplexAt.smul_def] at h
  have h' := congrArg (ofComplex σ).symm h
  rw [map_mul, AlgEquiv.symm_apply_apply, map_zero, mul_eq_zero] at h'
  rcases h' with h' | h'
  · exact absurd h' ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr ha))
  · exact (ofComplex σ).symm.injective (h'.trans (map_zero _).symm)

theorem linearIndependent_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) :
    LinearIndependent (𝓞 K) (fun _ : Unit ↦ (1 : ComplexAt σ)) :=
  LinearIndependent.of_subsingleton' () fun r hr ↦ by
    by_contra h
    have h1 := congrArg (ofComplex σ).symm (complexAt_smul_eq_zero h hr)
    rw [map_one, map_zero] at h1
    exact one_ne_zero h1

example : IsReduced (base (𝓞 ℚ) 1).X := inferInstance
example : IsInvertibleSheaf (baseBundle (𝓞 ℚ) 1).L := (baseBundle (𝓞 ℚ) 1).invertible
example : LinearIndependent (𝓞 ℚ) (fun _ : Unit ↦ (1 : ComplexAt (Rat.castHom ℂ))) :=
  linearIndependent_one _
example : ∀ x : (base (𝓞 ℚ) 1).complexPoints (intEmb (Rat.castHom ℂ)),
    ∑ _i : Unit, (ofComplex (Rat.castHom ℂ)).symm 1 •
      (base (𝓞 ℚ) 1).evalGlobalSection (baseBundle (𝓞 ℚ) 1).L x 0 = 0 := fun x ↦ by simp

example : Algebra.FiniteType (𝓞 ℚ) (𝓞 ℚ) := inferInstance
example : IsReduced (𝓞 ℚ) := inferInstance
example : ∀ φ : 𝓞 ℚ →+* ℂ, φ.comp (algebraMap (𝓞 ℚ) (𝓞 ℚ)) = intEmb (Rat.castHom ℂ) →
    ∑ _i : Unit, (ofComplex (Rat.castHom ℂ)).symm 1 * φ 0 = 0 := fun φ _ ↦ by simp

example (p : (base (𝓞 ℚ) 1).X) : p ∈ (⊤ : (base (𝓞 ℚ) 1).X.Opens) := trivial

example : ∀ p : (base (𝓞 ℚ) 1).X, ∃ U : (base (𝓞 ℚ) 1).X.Opens, p ∈ U ∧ ∃ d : 𝓞 ℚ, d ≠ 0 ∧
    resM ((preMod (base (𝓞 ℚ) 1).X).obj (baseBundle (𝓞 ℚ) 1).L) (le_top : U ≤ ⊤)
      (d • (0 : (base (𝓞 ℚ) 1).H0 (baseBundle (𝓞 ℚ) 1).L)) = 0 :=
  fun p ↦ ⟨⊤, trivial, 1, one_ne_zero, by rw [smul_zero]; exact resM_zero _ _⟩

end ProjScheme

end

end GroundTheory.Heights₂.Heights
