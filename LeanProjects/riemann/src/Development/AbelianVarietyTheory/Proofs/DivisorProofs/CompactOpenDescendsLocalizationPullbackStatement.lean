import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenDescendsLocalizationPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_open_descends_localization_pullback : ∀ (R : Type) [CommRing R] (q : PrimeSpectrum R) (T : Scheme.{0}) (π : T ⟶ Sp R) (U' : (pullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))).Opens), IsCompact (U' : Set (pullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) : Scheme.{0})) → ∃ U₀ : T.Opens, IsCompact (U₀ : Set T) ∧ pullback.fst π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) ⁻¹ᵁ U₀ = U' := by
  first | exact @GlobalTheory.exists_isCompact_open_preimage_eq_baseChange_atPrime | exact GlobalTheory.exists_isCompact_open_preimage_eq_baseChange_atPrime | (intros; apply GlobalTheory.exists_isCompact_open_preimage_eq_baseChange_atPrime <;> assumption)
