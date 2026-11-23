import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.IntAdd

theorem formalGroupLawCoboundaryOne_map_coefficients {R S : Type} [CommRing R] [CommRing S] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : ∀ i, constantCoeff (μ i) = 0) (r : R →+* S)
    (f : MvPowerSeries (Fin d) R) :
    map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero h),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem eq_zero_of_cob1_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ s : MvPowerSeries (Fin d) O, cob1 (up E c.μ) (map (algebraMap O E) s) = 0 → s = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hF s hs
  have h0 : cob1 c.μ s = 0 := by
    have hm := formalGroupLawCoboundaryOne_map_coefficients c.μ c.isLaw.const (algebraMap O E) s
    have hup : (fun i => map (algebraMap O E) (c.μ i)) = up E c.μ := rfl
    rw [hup, hs] at hm
    ext α
    apply hF.inj
    have := congrArg (coeff α) hm
    rw [coeff_map] at this
    rw [this]; simp
  have hp : (p : O) ≠ 0 := by
    intro h
    exact one_ne_zero (hF.sat 1 (by rw [h, zero_mul]))
  have hev : ∀ n, c.ev n s = 0 := fun n =>
    G.eq_zero_of_cobOne_eq_zero hp n (by
      rw [← (Chart.ev₂_eval p O G d c n s).2.2.2, h0, map_zero])
  ext α
  rw [coeff_zero]
  refine hF.eq_zero_of_forall_pow_dvd fun m => ?_
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact hn s (hev n) α (Nat.lt_succ_self _)

end GlobalTheory.QLog.IntAdd
