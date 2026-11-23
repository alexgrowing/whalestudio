import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationBoundOverDvr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramification_bound_over_dvr : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (O : Type) [CommRing O] (β : O →+* K), Function.Injective β → (∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1) → ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O), (letI := β.toAlgebra; IsFractionRing O K) ∧ ∀ (T : CDVR) (io : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b → (algebraMap T.V T.Fr).comp b = io.comp β → ∃ e : ℕ, OverLa la T.V io e := by
  first | exact @GlobalTheory.PlaceLocalRing.dvr_and_overLa | exact GlobalTheory.PlaceLocalRing.dvr_and_overLa | (intros; apply GlobalTheory.PlaceLocalRing.dvr_and_overLa <;> assumption)
