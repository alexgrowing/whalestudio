import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsProjOver)

namespace UpperTheory.Et

def WeilAt (l : ℕ) [Fact l.Prime] {F : Type} [Field F] [Fintype F] (Ω : Type) [Field Ω] [Algebra F Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of F)) (φ : Ω ≃ₐ[F] Ω) (i : ℕ) : Prop :=
  ∃ (_ : FiniteDimensional ℚ_[l] (HQ l (sch.obj (GlobalTheory.Et.geom Ω p)) i 0)) (P : Polynomial ℚ),
    P.map (algebraMap ℚ ℚ_[l]) = LinearMap.charpoly (galHQ l Ω p i 0 φ⁻¹) ∧
    ∀ z ∈ (P.map (algebraMap ℚ ℂ)).roots, ‖z‖ = (Fintype.card F : ℝ) ^ ((i : ℝ) / 2)

def WeilOneD : Prop := ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [Fintype F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω],
  IsUnit (l : F) → ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of F)), SmoothOfRelativeDimension d p → IsProjOver p →
  ∀ φ : Ω ≃ₐ[F] Ω, (∀ x, φ x = x ^ Fintype.card F) → ∀ i : ℕ, WeilAt l Ω p φ i

def WeilOneP : Prop := ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [Fintype F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω],
  IsUnit (l : F) → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of F)), Smooth p → IsProjOver p →
  ∀ φ : Ω ≃ₐ[F] Ω, (∀ x, φ x = x ^ Fintype.card F) → ∀ i : ℕ, WeilAt l Ω p φ i

def pwSum {K : Type*} [CommSemiring K] (a : Multiset K) (r : ℕ) : K := (a.map (· ^ r)).sum

end UpperTheory.Et

end
