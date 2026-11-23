import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.IntEmb

theorem ringOfIntegers_embedding_mem_range
    (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [IsIntegrallyClosed A] (E : Type) [Field E] [NumberField E] (σ : E →+* Ω) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A Ω).range := by
  have hℤ : IsIntegral ℤ (σ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom ℤ) σ (RingHom.ext_int _ _)
      (NumberField.RingOfIntegers.isIntegral_coe a)
  have hA : IsIntegral A (σ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom A) (RingHom.id Ω) (RingHom.ext_int _ _) hℤ
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp hA
  exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.Ar.IntEmb
