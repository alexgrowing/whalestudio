import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinear

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.IterateLocal

open MvPowerSeries in
set_option autoImplicit false in
private lemma iterate_invDer_sub (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) :
    ∀ (m : ℕ) (F G : MvPowerSeries (Fin d) R),
      (_root_.GlobalTheory.LawDer.invDer μ u)^[m] F - (_root_.GlobalTheory.LawDer.invDer μ u)^[m] G =
        (_root_.GlobalTheory.LawDer.invDer μ u)^[m] (F - G) := by
  have hadd := (_root_.GlobalTheory.LawDer.Linear.invDer_linear R d μ hμ u).1
  intro m
  induction m with
  | zero => intro F G; rfl
  | succ m ih =>
    intro F G
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    rw [sub_eq_iff_eq_add, ← hadd, sub_add_cancel]

open MvPowerSeries in
set_option autoImplicit false in
private lemma coeff_iterate_invDer_eq_zero_of_degree_lt (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (N : ℕ) :
    ∀ (m : ℕ) (H : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree < N + m → coeff α H = 0) →
      ∀ α : Fin d →₀ ℕ, α.degree < N →
        coeff α ((_root_.GlobalTheory.LawDer.invDer μ u)^[m] H) = 0 := by
  intro m
  induction m with
  | zero => intro H hH α hα; exact hH α (by simpa using hα)
  | succ m ih =>
    intro H hH α hα
    rw [Function.iterate_succ_apply]
    refine ih _ (fun β hβ => ?_) α hα
    exact _root_.GlobalTheory.invDer_coeff_eq_zero_of_degree_lt R d μ hμ u H (N + m)
      (fun γ hγ => hH γ (by omega)) β hβ

open MvPowerSeries in
set_option autoImplicit false in

theorem _root_.GlobalTheory.LawDer.IterateLocal.constantCoeff_iterate_invDer_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (n : ℕ) (F G : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree ≤ n → coeff α F = coeff α G) → constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[n] F) = constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[n] G) := by
  intro R _ d μ hμ u n F G hFG
  rw [← sub_eq_zero, ← map_sub, iterate_invDer_sub R d μ hμ u,
    ← coeff_zero_eq_constantCoeff_apply]
  refine coeff_iterate_invDer_eq_zero_of_degree_lt R d μ hμ u 1 n (F - G) (fun α hα => ?_) 0
    (by simp)
  rw [map_sub, hFG α (by omega), sub_self]

end GlobalTheory.LawDer.IterateLocal
