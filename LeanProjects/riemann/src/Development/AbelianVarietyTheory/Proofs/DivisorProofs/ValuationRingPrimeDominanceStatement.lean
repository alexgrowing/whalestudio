import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingPrimeDominance
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_ring_prime_dominance : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (A : Type) [CommRing A] [Algebra O A] [Algebra.FiniteType O A] (K : Type) [Field K] [Algebra A K] [Algebra O K] [IsScalarTower O A K], Function.Injective (algebraMap O K) → (∀ x : K, ∃ a b : A, algebraMap A K b ≠ 0 ∧ x * algebraMap A K b = algebraMap A K a) → ∀ p : Ideal A, p.IsPrime → RingHom.ker (algebraMap A K) ≤ p → (maximalIdeal O).map (algebraMap O A) ≤ p → ∀ d : ℕ, (d : Cardinal) ≤ Algebra.trdeg O K → ∃ (T : CDVR) (f : A →+* T.V) (ψ : K →+* T.Fr), (algebraMap T.V T.Fr).comp f = ψ.comp (algebraMap A K) ∧ IsLocalHom (f.comp (algebraMap O A)) ∧ TrdegGe ((maximalIdeal T.V).comap f).ResidueField d := by
  first | exact @GlobalTheory.GenericCentre.exists_cdvr_centred_generic | exact GlobalTheory.GenericCentre.exists_cdvr_centred_generic | (intros; apply GlobalTheory.GenericCentre.exists_cdvr_centred_generic <;> assumption)
