import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc.QAlg

theorem exists_const_add_dQ_mul (B : Type) [CommRing B] (m : ℕ) (x : Jet B Unit m) :
    ∃ (b : B) (y : Jet B Unit m), x = algebraMap B _ b + dQ B m * y := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig B Unit ^ (m + 1)) x
  have hmem := sub_const_mem_orig P
  have hr : Set.range (MvPolynomial.X : Unit → MvPolynomial Unit B) = {MvPolynomial.X ()} :=
    Set.range_unique
  rw [orig, hr, Ideal.mem_span_singleton'] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  refine ⟨MvPolynomial.constantCoeff P, Ideal.Quotient.mk _ Q, ?_⟩
  have hP : P = MvPolynomial.C (MvPolynomial.constantCoeff P) + Q * MvPolynomial.X () := by
    rw [hQ]; ring
  conv_lhs => rw [hP]
  rw [map_add, map_mul, mul_comm]
  rfl

theorem jetAug_dQ (B : Type) [CommRing B] (m : ℕ) :
    (jetAug : Jet B Unit m →ₐ[B] B) (dQ B m) = 0 := by
  show (jetAug : Jet B Unit m →ₐ[B] B)
    (Ideal.Quotient.mk (orig B Unit ^ (m + 1)) (MvPolynomial.X ())) = 0
  simp [jetAug, liftJet, Ideal.Quotient.liftₐ_apply]

theorem add_pow_of_natCast_eq_zero {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime)
    (h : (p : A) = 0) (x y : A) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp, h]
  simp

theorem pow_eq_one_add (B : Type) [CommRing B] (p : ℕ) [hp : Fact p.Prime] (h0 : (p : B) = 0)
    (e : Jet B Unit p) (he : (jetAug : Jet B Unit p →ₐ[B] B) e = 1) :
    ∃ v : B, e ^ p = 1 + dQ B p ^ p * algebraMap B _ (v ^ p) := by
  have hpJ : ((p : ℕ) : Jet B Unit p) = 0 := by
    rw [← map_natCast (algebraMap B (Jet B Unit p)) p, h0, map_zero]
  obtain ⟨b, y, rfl⟩ := exists_const_add_dQ_mul B p e
  have hb : b = 1 := by
    simpa only [map_add, map_mul, jetAug_dQ, zero_mul, add_zero, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply] using he
  subst hb
  obtain ⟨c, z, rfl⟩ := exists_const_add_dQ_mul B p y
  refine ⟨c, ?_⟩
  have h2 : dQ B p ^ p * dQ B p ^ p = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (by have := hp.out.one_lt; omega) (dQ_pow B p)
  rw [map_one, add_pow_of_natCast_eq_zero p hp.out hpJ, one_pow, mul_pow,
    add_pow_of_natCast_eq_zero p hp.out hpJ, mul_pow, map_pow]
  linear_combination (z ^ p) * h2

end GlobalTheory.CompanionTheory.Ar.Coc.QAlg
