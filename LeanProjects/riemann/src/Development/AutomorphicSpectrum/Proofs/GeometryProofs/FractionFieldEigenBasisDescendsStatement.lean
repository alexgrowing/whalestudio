import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldEigenBasisDescends
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fraction_field_eigen_basis_descends : ∀ (E : Type) [Field E] [NumberField E] (K C V A : Type) [Field K] [CharZero K] [Field C] [CharZero C] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra V K] [IsFractionRing V K] [CommRing A] [IsDomain A] [Algebra A C]
    (j : K →+* C) (g n : ℕ) (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (σ : E →+* K) (b : Fin n → Fin g → K),
    (∀ a : K, a ∈ (algebraMap V K).range → j a ∈ (algebraMap A C).range) →
    (∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i)) →
    LinearIndependent K b → Submodule.span V (Set.range b) = HT.eigSub ρK σ (stdLat V K g) →
    LinearIndependent C (fun i k => j (b i k)) ∧
      Submodule.span C (Set.range fun i k => j (b i k)) = HT.eigSp ρC (j.comp σ) ∧
      Submodule.span A (Set.range fun i k => j (b i k)) = HT.eigSub ρC (j.comp σ) (stdLat A C g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig.eigSub_baseChange | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig.eigSub_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig.eigSub_baseChange <;> assumption)
