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

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem embeddings_padicComplex : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes),
    (∀ (s : E →+* ℂ_[p]) (a : 𝓞 E), s (a : E) ∈ (algebraMap (OCp p) ℂ_[p]).range) ∧
      Nat.card (E →+* ℂ_[p]) = Module.finrank ℚ E := by
  intro E _ _ p
  refine ⟨fun s a => ?_, ?_⟩
  · have hO : IsIntegral (OCp p) (s (a : E)) :=
      (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (Int.castRingHom (OCp p)) s (RingHom.ext_int _ _)
    have hv := Valuation.valuationSubring.integers (v := NormedField.valuation (K := ℂ_[p]))
    exact hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.mp hO)
  · rw [Nat.card_eq_fintype_card]
    exact NumberField.Embeddings.card E ℂ_[p]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
