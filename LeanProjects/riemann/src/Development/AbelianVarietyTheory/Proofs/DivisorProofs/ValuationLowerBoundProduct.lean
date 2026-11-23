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

namespace GlobalTheory.ValArith
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem ord_mul (x y : FractionRing R) (hx : x ≠ 0) (hy : y ≠ 0) :
    ord_vw R (x * y) = ord_vw R x + ord_vw R y := by
  unfold ord_vw
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]
  ring

theorem ord_inv (x : FractionRing R) (hx : x ≠ 0) : ord_vw R x⁻¹ = -ord_vw R x := by
  have h := ord_mul x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx] at h
  have h1 : ord_vw R (1 : FractionRing R) = 0 := by simp [ord_vw]
  omega

theorem ord_unit (u : Rˣ) : ord_vw R (algebraMap R (FractionRing R) (u : R)) = 0 := by
  unfold ord_vw
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.2 fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm u.isUnit]
  simp

theorem ord_pos (l : ℕ) (hm : (l : R) ∈ IsLocalRing.maximalIdeal R) (h0 : (l : R) ≠ 0) :
    0 < ord_vw R ((l : ℕ) : FractionRing R) := by
  have h0' : ((l : ℕ) : FractionRing R) ≠ 0 := by
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h0
  have h1 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) ((l : ℕ) : FractionRing R) < 1 := by
    rw [← map_natCast (algebraMap R (FractionRing R)), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hm
  have h2 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) ((l : ℕ) : FractionRing R) ≠ 0 := by
    simpa using h0'
  rw [← WithZero.exp_log h2, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold ord_vw
  omega

theorem val_sq_div_ge : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ),
    (l : R) ∈ IsLocalRing.maximalIdeal R → (l : R) ≠ 0 →
    ∀ (a b δ : FractionRing R) (u : Rˣ) (ca cd : ℚ), a ≠ 0 → b ≠ 0 → δ ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l a ≤ (ca : WithTop ℚ) → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l b ≤ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l δ = (cd : WithTop ℚ) →
      ((-(ca + cd) : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l ((algebraMap R (FractionRing R) (u : R)) ^ 2 / (a * (δ * b))) := by
  intro R _ _ _ l hm h0 a b δ u ca cd ha hb hd hva hvb hvd
  have hL := ord_pos (R := R) l hm h0
  set L : ℚ := (ord_vw R ((l : ℕ) : FractionRing R) : ℚ) with hLdef
  have hLq : (0 : ℚ) < L := by rw [hLdef]; exact_mod_cast hL
  set w := algebraMap R (FractionRing R) (u : R) with hw
  have hw0 : w ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 u.ne_zero
  have hx0 : w ^ 2 / (a * (δ * b)) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero 2 hw0) (mul_ne_zero ha (mul_ne_zero hd hb))
  have hord : ord_vw R (w ^ 2 / (a * (δ * b))) = -(ord_vw R a + ord_vw R δ + ord_vw R b) := by
    rw [div_eq_mul_inv, pow_two, ord_mul _ _ (mul_ne_zero hw0 hw0) (inv_ne_zero (mul_ne_zero ha (mul_ne_zero hd hb))),
      ord_mul _ _ hw0 hw0, ord_inv _ (mul_ne_zero ha (mul_ne_zero hd hb)), ord_mul _ _ ha (mul_ne_zero hd hb),
      ord_mul _ _ hd hb, hw, ord_unit]
    ring
  simp only [val_vp, if_neg ha, if_neg hb, if_neg hd, if_neg hx0] at hva hvb hvd ⊢
  rw [← hLdef] at hva hvb hvd ⊢
  have h1 : (ord_vw R a : ℚ) / L ≤ ca := by exact_mod_cast hva
  have h2 : (ord_vw R b : ℚ) / L ≤ 0 := by exact_mod_cast hvb
  have h3 : (ord_vw R δ : ℚ) / L = cd := by exact_mod_cast hvd
  rw [hord]
  have e : ((-(ord_vw R a + ord_vw R δ + ord_vw R b) : ℤ) : ℚ) / L
      = -((ord_vw R a : ℚ) / L) - (ord_vw R δ : ℚ) / L - (ord_vw R b : ℚ) / L := by
    push_cast; ring
  rw [e]
  exact_mod_cast (by linarith : -(ca + cd) ≤ -((ord_vw R a : ℚ) / L) - (ord_vw R δ : ℚ) / L - (ord_vw R b : ℚ) / L)

end GlobalTheory.ValArith
