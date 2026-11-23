import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneTmulQuotReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesLiftQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeriesOfAdditiveFunctionFirstLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePowStatement

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

set_option maxHeartbeats 1000000 in

theorem exists_series_of_cobOne_dvd : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 ∧ (∀ α, (p : O) ∣ coeff α (cob2 c.μ κ)) ∧ (∀ α, (p : O) ∣ coeff α (Katz.swap κ - κ)) ∧ (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) ∧ c.ev 1 B = b + (p : O) • y := by
  intro p _ O _ G d c b z hbz
  let I : Ideal O := Ideal.span {(p : O)}
  have hpI : (p : O) ^ 1 ∈ I := by rw [pow_one]; exact Ideal.subset_span rfl
  obtain ⟨c', hlaw, hev, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 hpI
  have hmkp : (algebraMap O (O ⧸ I)) (p : O) = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  have hb' : cobOne (O ⧸ I) ((G.baseChange (O ⧸ I)).A 1) ((G.toBase (O ⧸ I)).app 1 b) = 0 := by
    rw [← SemiBialgHom.two_cobOne, hbz, map_smulₛₗ, hmkp, zero_smul]
  obtain ⟨κ', B', hcoc, hκ0, hcob, hev1⟩ := GlobalTheory.T.exists_series_of_additive_function_first_level p (O ⧸ I) d _ c' _ hlaw _ hb'
  obtain ⟨hl2, hz2, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I
  obtain ⟨hl1, hz1, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ (Fin d ⊕ Fin d)) I
  obtain ⟨hl0, -, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I
  obtain ⟨κ, hκ, hκc⟩ := hl2 κ'
  obtain ⟨B, hB, -⟩ := hl0 B'
  have hdiv : ∀ x : O, x ∈ I ↔ (p : O) ∣ x := fun x => Ideal.mem_span_singleton
  have hμ := c.isLaw.const
  obtain ⟨hm1, hm2, hsw, -, hpull⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hμ (O ⧸ I) (Ideal.Quotient.mk I)
  obtain ⟨-, hn⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) (Ideal.Quotient.mk I)
  have hnm : (fun i => map (Ideal.Quotient.mk I) (nmul c.μ p i)) =
      nmul (fun i => map (Ideal.Quotient.mk I) (c.μ i)) p := funext fun i => (hn p i).2
  obtain ⟨hpl, -⟩ := hpull (nmul c.μ p) fun i => (hn p i).1
  have hy : ∃ y : G.A 1, c.ev 1 B = b + (p : O) • y := by
    have h1 : (G.toBase (O ⧸ I)).app 1 (c.ev 1 B) = (G.toBase (O ⧸ I)).app 1 b := by
      rw [← hev, hB, hev1]
    rw [toBase_app, toBase_app] at h1
    have h2 : (1 : O ⧸ I) ⊗ₜ[O] (c.ev 1 B - b) = 0 := by rw [tmul_sub, h1, sub_self]
    obtain ⟨-, hq, hs⟩ := GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A 1) I
    obtain ⟨y, hy⟩ := (hs (p : O) _).1 ((hq _).1 h2)
    exact ⟨y, by rw [← hy]; abel⟩
  obtain ⟨y, hy⟩ := hy
  refine ⟨κ, B, y, hκc hκ0, ?_, ?_, ?_, hy⟩
  · intro α
    refine (hdiv _).1 ((hz1 _).1 ?_ α)
    rw [hm2, hκ]; exact hcoc.1
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hsw, hκ, hcoc.2, sub_self]
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hm1, hpl, hκ, hB, hnm, hcob, sub_self]

end GlobalTheory.QLog
