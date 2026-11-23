import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicDerivationLocalizationAtPrimeSpanOfRi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logarithmicDerivation_localizationAtPrime_span_of_ring : ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (I : Ideal A) (n : ℕ) (b : Fin n → Derivation ℤ A A), (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∀ D' : Derivation F R R, (∀ f ∈ I.map (algebraMap A R), D' f ∈ I.map (algebraMap A R)) → ∃ c : Fin n → R, ∀ a : A, D' (algebraMap A R a) = ∑ j, c j * algebraMap A R (b j a) := by
  first | exact @GlobalTheory.logDerivation_atPrime_span | exact GlobalTheory.logDerivation_atPrime_span | (intros; apply GlobalTheory.logDerivation_atPrime_span <;> assumption)
