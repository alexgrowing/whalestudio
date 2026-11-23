import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.Linear

variable {R : Type} [CommRing R] {d : ℕ}

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in

theorem _root_.GlobalTheory.LawDer.Linear.invDer_linear : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ u : Fin d → R, (∀ F G : MvPowerSeries (Fin d) R, _root_.GlobalTheory.LawDer.invDer μ u (F + G) = _root_.GlobalTheory.LawDer.invDer μ u F + _root_.GlobalTheory.LawDer.invDer μ u G) ∧ (∀ (a : R) (F : MvPowerSeries (Fin d) R), _root_.GlobalTheory.LawDer.invDer μ u (a • F) = a • _root_.GlobalTheory.LawDer.invDer μ u F) ∧ ∀ a : R, _root_.GlobalTheory.LawDer.invDer μ u (C a) = 0 := by
  intro R _ d μ hμ u
  have hμs : HasSubst μ := hasSubst_of_constantCoeff_nilpotent fun i ↦ by simp [hμ i]
  have hzero : HasSubst (Sum.elim (fun i : Fin d ↦ (X i : MvPowerSeries (Fin d) R))
      fun _ : Fin d ↦ (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_nilpotent fun s ↦ by cases s <;> simp
  refine ⟨fun F G ↦ ?_, fun a F ↦ ?_, fun a ↦ ?_⟩
  · unfold _root_.GlobalTheory.LawDer.invDer _root_.GlobalTheory.LawDer.atZero
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [subst_add hμs, map_add, subst_add hzero, smul_add]
  · unfold _root_.GlobalTheory.LawDer.invDer _root_.GlobalTheory.LawDer.atZero
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [subst_smul hμs, Derivation.map_smul_of_tower, subst_smul hzero, smul_comm]
  · unfold _root_.GlobalTheory.LawDer.invDer _root_.GlobalTheory.LawDer.atZero
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [subst_C, pderiv_C]
    simpa using congrArg (u i • ·) (subst_C (a := Sum.elim
      (fun j : Fin d ↦ (X j : MvPowerSeries (Fin d) R))
      fun _ : Fin d ↦ (0 : MvPowerSeries (Fin d) R)) (0 : R))

end GlobalTheory.LawDer.Linear
