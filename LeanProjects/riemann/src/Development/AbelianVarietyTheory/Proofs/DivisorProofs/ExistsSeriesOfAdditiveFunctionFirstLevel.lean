import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocycles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLawStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.Chart

theorem exists_series_of_cobOne_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ)
    (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ b : G.A 1, cobOne k (G.A 1) b = 0 →
    ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k),
      IsCoc μ κ ∧ constantCoeff κ = 0 ∧ cob1 μ B = pull2 (nmul μ p) κ ∧ c.ev 1 B = b := by
  intro p _ k _ d G c μ hμ b hb
  obtain ⟨x, cc, B, -, hcob, hcounit, hB1⟩ := PDivGroup.exists_of_cobOne_eq_zero (G := G) hb
  have hfun := Chart.functions_are_series p k d G c
  have hsq := chart_square_presents p k d G c
  obtain ⟨Bs, hBs, -⟩ := hfun.2.2 B.1 B.2
  obtain ⟨κ, hκ, -⟩ := hsq.2 cc.1 (fun n => (cc.2 n).2)
  have hlaw := (LawCoord.main p k d G c).2 μ hμ
  have hcoc : IsCoc μ κ := (isCoc_iff_mem_cocycles p k d G c μ hμ κ).2 (by
    have e : (fun n => c.ev₂ n κ) = cc.1 := funext hκ
    rw [e]; exact cc.2)
  have hmap := (isMapOf_existsUnique_and p k d d G G c c ((p : ℤ_[p]) • 𝟙 G)).2 (nmul μ p)
    (GlobalTheory.T.isMapOf_natMultiple_formalGroupLaw p k d G c μ hμ p)
  have hid : cob1 μ Bs = pull2 (nmul μ p) κ := by
    obtain ⟨s, -, hs⟩ := hsq.2 (fun n => c.ev₂ n (cob1 μ Bs)) (fun n => hfun.2.1 n _)
    refine (hs _ fun n => rfl).trans (hs _ fun n => ?_).symm
    rw [(hmap.2 n).2, hκ, (hlaw.2 n Bs).2, hBs]
    exact (congrArg (fun z : G.cocycles => z.1 n) hcob).symm
  have hB0 : constantCoeff Bs = 0 := by
    have h := (counit_dUnit_evA k d (G.A 1) (c.x 1) (c.nil 1) (c.aug 1) Bs).1
    rw [← h]
    change Coalgebra.counit (R := k) (c.ev 1 Bs) = 0
    rw [hBs 1, hB1, hcounit]
  have hX : ∀ (σ : Type) (i : σ), constantCoeff (X i : MvPowerSeries σ k) = 0 :=
    fun _ i => constantCoeff_X i
  have hL : ∀ j, constantCoeff (inL (nmul μ p j)) = 0 := fun j => by
    unfold inL
    rw [SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hmap.1 j]
  have hR : ∀ j, constantCoeff (inR (nmul μ p j)) = 0 := fun j => by
    unfold inR
    rw [SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hmap.1 j]
  have hκ0 : constantCoeff κ = 0 := by
    have h1 := (SubstCalc.powerSeriesEvalTwoGroups_rules_alt k d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) _ _ hL hR).2.2.2.1 κ
    have h2 : constantCoeff (cob1 μ Bs) = 0 := by
      unfold cob1 inL inR
      rw [map_sub, map_sub, SubstCalc.constantCoeff_subst_of_zero hlaw.1,
        SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _),
        SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hB0, sub_zero, sub_zero]
    rw [← h1, ← h2, hid]
    rfl
  exact ⟨κ, Bs, hcoc, hκ0, hid, (hBs 1).trans hB1⟩

end GlobalTheory.Katz.Chart
