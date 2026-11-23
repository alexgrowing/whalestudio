import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldEmbeddingsIntoCpIntegral
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
theorem _root_.GlobalTheory.T.number_field_embeddings_into_cp_integral : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes),
    (∀ (s : E →+* ℂ_[p]) (a : 𝓞 E), s (a : E) ∈ (algebraMap (OCp p) ℂ_[p]).range) ∧
      Nat.card (E →+* ℂ_[p]) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.embeddings_padicComplex | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.embeddings_padicComplex | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.embeddings_padicComplex <;> assumption)
