import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

theorem map_pderiv_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries σ R) (s : σ) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv R s f) = MvPowerSeries.pderiv S s (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map,
    map_mul, map_add, map_natCast, map_one]

theorem map_atZero {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (H : MvPowerSeries (Fin d ⊕ Fin d) R) : map f (atZero H) = atZero (map f H) := by
  unfold atZero
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp))]
  congr 1
  funext s
  cases s <;> simp

theorem map_smul_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R)
    (H : MvPowerSeries σ R) : map f (a • H) = f a • map f H := by
  ext m
  simp [MvPowerSeries.coeff_map, MvPowerSeries.coeff_smul]

theorem map_invDer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (F : MvPowerSeries (Fin d) R) :
    map f (invDer μ u F) = invDer (fun i => map f (μ i)) (fun i => f (u i)) (map f F) := by
  unfold invDer
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul_coeffChange, map_atZero, map_pderiv_coeffChange, map_subst (hasSubst_of_constantCoeff_zero hμ)]

theorem map_invDer_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R),
    map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  intro R S _ _ f d μ hμ u k F
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_invDer f μ hμ, ih]

end GlobalTheory.LawDer
