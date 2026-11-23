import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupCocycleCoboundaryModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem exists_int_cob_dvd_of_defect_ev :
    ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  intro p _ O E _ _ _ hF G d c f s y hQL hs hy
  obtain ⟨hf0, -, hcob⟩ := hQL
  choose bκ _ hbκ using hcob
  set κ : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => bκ α with hκdef
  have hκ : map (algebraMap O E) κ = cob1 (up E c.μ) f := by
    ext α
    rw [coeff_map, hbκ α]
    rfl
  obtain ⟨hcoc, hκ0, hdef⟩ := GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hrel := (hdef p s hs).1
  have hμ0 := c.isLaw.const
  have hneg : cob1 c.μ (-s) = -cob1 c.μ s := by
    rw [← neg_one_smul O s, formalCoboundary_smul hμ0, neg_one_smul]
  obtain ⟨t, ht0, htd⟩ := GlobalTheory.T.formalGroupCocycle_coboundary_mod_prime p O G d c κ (-s) (-y) (hκ0 hf0) hcoc
    (fun α => by
      rw [hneg, hrel, show -((p : O) • κ - pull2 (nmul c.μ p) κ) - pull2 (nmul c.μ p) κ
        = -((p : O) • κ) by ring, map_neg, coeff_smul]
      exact (Dvd.intro _ rfl).neg_right)
    (by rw [map_neg, hy, smul_neg])
  refine ⟨t, ht0, fun α => ⟨coeff α (κ - cob1 c.μ t), Ideal.mem_span_singleton.2 (htd α), ?_⟩⟩
  have hup0 : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ0, map_zero]
  have hadd := formalCoboundary_add hup0 (f - map (algebraMap O E) t) (map (algebraMap O E) t)
  rw [sub_add_cancel] at hadd
  have hmap := (GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hμ0 E (algebraMap O E)).1 t
  have hsub : cob1 (up E c.μ) (f - map (algebraMap O E) t) =
      map (algebraMap O E) (κ - cob1 c.μ t) := by
    rw [map_sub, hmap, hκ]
    exact eq_sub_of_add_eq hadd.symm
  rw [hsub, coeff_map]

end GlobalTheory.QLog
