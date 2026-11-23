import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionNumberFieldEquivStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

noncomputable def fractionRingRingEquiv (A L : Type) [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    [IsFractionRing A L] : L ≃+* FractionRing A :=
  (FractionRing.algEquiv A L).toRingEquiv.symm

noncomputable def ratEquivFractionZP (p : Nat.Primes) : ℚ ≃+* FractionRing (ZP p) :=
  letI : Algebra (ZP p) ℚ :=
    (IsLocalization.lift (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (S := ZP p)
      (g := algebraMap ℤ ℚ) (fun y => isUnit_iff_ne_zero.2 (by
        have hy : (y : ℤ) ≠ 0 := fun h => y.2 (h ▸ Ideal.zero_mem _)
        simpa using hy))).toAlgebra
  haveI : @IsScalarTower ℤ (ZP p) ℚ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsFractionRing (ZP p) ℚ :=
    IsFractionRing.isFractionRing_of_isLocalization
      (Ideal.span {((p : ℕ) : ℤ)}).primeCompl (ZP p) ℚ (Ideal.primeCompl_le_nonZeroDivisors _)
  fractionRingRingEquiv (ZP p) ℚ

theorem genFib_extTo_zp {K : Type} {ι : K → Type} (P : Ideal (MRing ι ℤ)) (p : Nat.Primes) :
    genFib (extTo (ZP p) P) =
      (extTo ℚ P).map (MvPolynomial.map ((ratEquivFractionZP p : ℚ ≃+* FractionRing (ZP p)) :
        ℚ →+* FractionRing (ZP p))) := by
  unfold genFib extTo
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun f => ?_
  simp only [RingHom.comp_apply, MvPolynomial.map_map]
  exact congrArg (fun φ : ℤ →+* FractionRing (ZP p) => MvPolynomial.map φ f) (RingHom.ext_int _ _)

theorem genNum_zp_eq_rat (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℤ)) (p : Nat.Primes) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ)
    (Q : List (K → ℤ)) :
    genNum (FractionRing (ZP p)) (genFib (extTo (ZP p) P)) cls H Q = genNum ℚ (extTo ℚ P) cls H Q := by
  unfold genNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [genFib_extTo_zp, GlobalTheory.T.intersection_number_field_equiv K ι ℚ (FractionRing (ZP p)) (ratEquivFractionZP p)]

end GlobalTheory.CompanionTheory.Ar.Num
