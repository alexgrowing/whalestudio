import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algDefStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.QBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.WeightOnDatum

theorem weight_on_datum : ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ DomW (T.Q.Dw j) (wtA w) ∧ (w.LastPos → Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) ∧ 1 ≤ WeightAlgebra.DF w) ∧ (∀ τ, (T.Q.Dw j).mult τ ≤ D.R.r) ∧ Fintype.card (Lt1 (T.Q.Dw j)) ≤ 2 * D.R.f * D.R.r ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ Module.finrank ℚ D.host.E = 2 * D.R.f := by
  intro D T hP j hj w
  obtain ⟨hDF, -, hPsi, hN, hwt⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hP j hj w
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  obtain ⟨hp, hq, -⟩ := hP.2.2.2 j hj
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hj2 := hj.2
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]; omega
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    exact Nat.succ_le_of_lt (by positivity)
  have hp0 : 0 < (D.R.sigW j).1 := by
    simp only [Ranks.sigW]; omega
  have hlast : w.LastPos → ∀ t, 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := fun hw t =>
    hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  refine ⟨hDF, ?_, fun hw => ⟨?_, ?_⟩, fun τ => ?_, ?_, hf, by omega, hfr⟩
  · intro τ i i' h
    exact (dom_wtA w).1 τ h
  · intro τ hτ _
    obtain ⟨t, rfl⟩ := (hPsi τ).1 hτ
    have hmult : (T.Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
      unfold Datum.mult
      have hτ' : (DV.tauEmb D t) (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
      rw [if_pos hτ', hp]
    rw [hmult, (hwt t _).1]
    unfold ext0
    rw [dif_pos (by omega)]
    exact hlast hw t
  · have ht : Nonempty D.what₂.Tau := by
      by_cases h : InPsi T.Q.H D.host.φ₀
      · obtain ⟨t, -⟩ := (hPsi _).1 h
        exact ⟨t⟩
      · obtain ⟨t, -⟩ := (hN _).1 h
        exact ⟨t⟩
    obtain ⟨t⟩ := ht
    unfold WeightAlgebra.DF WeightAlgebra.degP
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, w.aP τ i) + ∑ i, w.aM τ i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
    refine le_trans ?_ (Nat.le_add_right _ _)
    exact le_trans (hlast hw t) (Finset.single_le_sum (f := fun i => w.aP t i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  · rw [← hr, Datum.mult]
    split_ifs <;> omega
  · refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]

end GlobalTheory.WeightOnDatum
