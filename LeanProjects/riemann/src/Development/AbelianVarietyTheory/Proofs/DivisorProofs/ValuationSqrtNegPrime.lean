import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbeddingStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem val_vp_sqrt_neg_prime : ∀ (E : Type) [Field E] (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R],
    (l : R) ∈ IsLocalRing.maximalIdeal R → (∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : R)) →
    ∀ (d : ℕ), d.Prime → ∀ (δ : E), δ ^ 2 = -(d : E) → ∀ σ : E →+* FractionRing R,
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ δ) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
  intro E _ l _ R _ _ _ _ hl hu d hd δ hδ σ
  have hK : ∀ n : ℕ, n ≠ 0 → (n : FractionRing R) ≠ 0 := fun n hn => by
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (Nat.cast_ne_zero.2 hn)
  have hsq : (σ δ) ^ 2 = -(d : FractionRing R) := by rw [← map_pow, hδ, map_neg, map_natCast]
  have hx : σ δ ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hsq
    exact hK d hd.ne_zero hsq
  have h2 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (d : FractionRing R) = 2 * GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ δ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw
    rw [show (d : FractionRing R) = -((σ δ) ^ 2) by rw [hsq, neg_neg], Valuation.map_neg, map_pow, WithZero.log_pow]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  by_cases hld : l = d
  · subst hld
    have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
    have h1 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (l : FractionRing R) < 1 := by
      rw [← map_natCast (algebraMap R (FractionRing R)), IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hl
    have h2' : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (l : FractionRing R) ≠ 0 := by
      simpa using hK l hl0
    have h3 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (l : FractionRing R) ≠ 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw
      intro h4
      have := WithZero.exp_log h2'
      rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
      exact h1.ne this.symm
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ δ) ≠ 0 := by
      intro h6; rw [h2, h6, mul_zero] at h3; exact h3 rfl
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, if_neg hx, if_pos rfl, h2]
    congr 1
    push_cast
    field_simp
  · have hunit : IsUnit (d : R) := hu d hd (Ne.symm hld)
    have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (d : FractionRing R) = 1 := by
      rw [← map_natCast (algebraMap R (FractionRing R)), IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact fun hm => (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ hm hunit)
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (d : FractionRing R) = 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw; rw [hv]; simp
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ δ) = 0 := by omega
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, if_neg hx, if_neg hld, h5]
    simp

end GlobalTheory
