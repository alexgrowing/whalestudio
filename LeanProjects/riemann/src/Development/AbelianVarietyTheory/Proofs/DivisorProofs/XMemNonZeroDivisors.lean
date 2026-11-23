import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBasePeriodsFactorMulGeneratorStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.Taut

theorem X_mem_nonZeroDivisors (W : Type) [CommRing W] {σ : Type} (k : σ) :
    (MvPolynomial.X k : MvPolynomial σ W) ∈ nonZeroDivisors (MvPolynomial σ W) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun p hp => ?_, fun p hp => ?_⟩
  · ext m
    have := congrArg (MvPolynomial.coeff (m + Finsupp.single k 1)) hp
    rwa [mul_comm, MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this
  · ext m
    have := congrArg (MvPolynomial.coeff (m + Finsupp.single k 1)) hp
    rwa [MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this

theorem monomial_chart : ∀ {o : Type} [CommRing o] {ζ : o} (g n : ℕ) (φ : InvFun ℤ), 1 ≤ n → ∀ C : Taut ζ g n φ,
    C.Q.IsMonomialTau C.t (fun k => (n : ℤ) • C.δ k) ∧ Module.finrank ℤ C.Q.X ≤ g ∧ IsCone id φ C.δ ∧
      (∀ z, z ≠ 0 → ∃ k, 0 < C.δ k z z) ∧ (∀ k, C.t k ≠ 0) := by
  intro o _ ζ g n φ _ C
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    obtain ⟨k, hk, hc⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator C.T (C.ψ.comp MvPolynomial.C) (fun k => C.ψ (MvPolynomial.X k))
      (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.Q C.e C.data a b
    let z : Fin C.N → ℤ := fun j => (n : ℤ) * (C.ε (.inr j) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)
    let w : C.Rˣ := ∏ j, (C.tor j).unit ^ z j
    refine ⟨k * Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹, ?_,
      GlobalTheory.PolDeg.Taut.tauCoord_mul_unit hc w⁻¹⟩
    rw [Units.val_mul, hk, Fintype.prod_sum_type]
    have hw : ((Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹ : (FractionRing C.R)ˣ) : FractionRing C.R) *
        ∏ j : Fin C.N, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inr j))) ^ z j = 1 := by
      rw [← Units.val_one, ← mul_inv_cancel (Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w)]
      simp [w, map_prod, Units.coe_prod, map_zpow]
      refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ?_)
      exact (map_ne_zero_iff _ (IsFractionRing.injective C.R (FractionRing C.R))).2 (C.tor j).ne_zero
    have hl : ∏ i, algebraMap C.R (FractionRing C.R) (C.t i) ^ (((n : ℤ) • C.δ i) a b) =
        ∏ k : Fin C.m, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inl k))) ^
          ((n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)) := by
      rfl
    rw [hl, _root_.mul_assoc, mul_comm (∏ j : Fin C.N, _), hw, _root_.mul_one]
  · have h : Module.finrank ℤ C.Q.X = C.T.r := by
      rw [C.e.toIntLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    have := C.genus
    omega
  · exact C.cone.pull_equiv C.e.toIntLinearEquiv
  · intro z hz
    obtain ⟨k, hk⟩ := C.defin (C.e z) (by simpa using hz)
    exact ⟨k, hk⟩
  · intro k hk
    letI := C.ψ.toAlgebra
    haveI : Module.Flat (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R := C.compl.2.2.1
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := C.R) (X_mem_nonZeroDivisors C.W (Sum.inl k : Fin C.m ⊕ Fin C.N))
    apply one_ne_zero (α := C.R)
    apply hreg
    show C.ψ (MvPolynomial.X (.inl k)) * 1 = C.ψ (MvPolynomial.X (.inl k)) * 0
    rw [show C.ψ (MvPolynomial.X (.inl k)) = 0 from hk]; simp

end GlobalTheory.TChart.Taut
