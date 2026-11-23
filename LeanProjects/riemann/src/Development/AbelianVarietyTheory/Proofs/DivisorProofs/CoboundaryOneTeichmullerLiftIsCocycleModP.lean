import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundariesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem cob2_cob1_lift_mem_intBy_and_swap_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ →
    ∀ f ∈ quasiInt p k (Fin d),
      cob2 (fun i => Katz.lift p (μ i)) (cob1 (fun i => Katz.lift p (μ i)) f) ∈ intBy p k _ p ∧
      swap (cob1 (fun i => Katz.lift p (μ i)) f) - cob1 (fun i => Katz.lift p (μ i)) f ∈
        intBy p k _ p := by
  intro p _ k _ _ _ d μ hμ f hf
  have hL : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  obtain ⟨hcc1, hcc2, -⟩ := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (fun i => Katz.lift p (μ i)) hL f
  have hred := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ hμ.const
  have hr := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)

  have hX3 : ∀ (j : Fin d ⊕ (Fin d ⊕ Fin d)),
      constantCoeff (X j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)) = 0 :=
    fun j => constantCoeff_X j
  have hx1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      ∀ i, constantCoeff (op (fun i => Katz.lift p (μ i)) a b i) = 0 := by
    intro a b ha hb i
    exact ((GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) d _ Empty a b ha hb).2.2.2.1 _).trans (hL i)
  refine ⟨?_, ?_⟩
  · rw [hcc1]
    have hA := hop x1 _ hx1 (hop x2 x3 hx2 hx3)
    have hB := hop _ x3 (hop x1 x2 hx1 hx2) hx3
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) _ _ (op μ x1 (op μ x2 x3)) f
      hA hB (fun i => (hred.2.2.1 i).1) (fun i => ?_) hf
    rw [← hμ.assoc]
    exact (hred.2.2.1 i).2
  · rw [hcc2]
    have hXs : ∀ (j : Fin d ⊕ Fin d),
        constantCoeff (X j : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
      fun j => constantCoeff_X j
    have hS : ∀ i, constantCoeff (swap (Katz.lift p (μ i))) = 0 := by
      intro i
      exact ((GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) d _ Empty _ _ (fun j => hXs _) (fun j => hXs _)).2.2.2.1 _).trans
        (hL i)
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ Fin d) _ _ μ f hS hL (fun i => ?_)
      (fun i => (hr.2.2.1 (μ i))) hf
    have := (hred.1 _ _ (hr.2.2.1 (μ i))).2
    rwa [hμ.comm i] at this

end GlobalTheory.Katz
