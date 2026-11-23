import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledTensorLatticeLeCompletedHomLatticeOffPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedMatrixGroupOfLocalMultiplier
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierShiftedLatticeAwayFromPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteAdeleOfSplitPlacesIdempotentSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel.OffTens

theorem partAt_finW_off_mem_hatA : ∀ (D : D7) (S T : HSp D) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ (L : Lt D.host.E T.rank) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E), y ∈ tens (stdL D.host.E S.rank) L → GlobalTheory.LiftLevel.partAt (1 - e - cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L)) := by
  intro D S T Pg Q e he L y hy
  classical
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum D _ e he
  have hf : 1 - e - cA D e = 1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by rw [hσ]; ring
  have hW : finW S T y = GlobalTheory.LiftLevel.TrOff.gm S T 1 y := rfl
  rw [hf, hW, GlobalTheory.LiftLevel.TrOff.partAt_gm, mul_one]
  have hO : ∀ (c : 𝓞 D.host.F), ∀ z ∈ tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L),
      (algebraMap D.host.F D.host.E (c : D.host.F)) • z ∈ tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L) :=
    fun c z hz => GlobalTheory.Ker.HatLat.smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hz
  have hγ : (1 - σ) ∈ intAf D.host.F := by
    intro w
    rw [map_sub, map_one]
    by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
    · obtain ⟨PP, hPP, rfl⟩ := hw
      rw [hσ1 PP hPP, sub_self]; exact zero_mem _
    · push_neg at hw
      rw [hσ0 w hw, sub_zero]; exact GlobalTheory.LatVac.one_mem_intAf _ w
  refine GlobalTheory.HatPoint.mem_hatA_of_div D S T _ hO _ hγ _ fun w => ?_
  by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
  · left
    obtain ⟨PP, hPP, rfl⟩ := hw
    rw [map_sub, map_one, hσ1 PP hPP, sub_self]
  · right
    push_neg at hw
    have hex : ∀ PP ∈ Pg ∪ Q, ∃ s : 𝓞 D.host.F,
        algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ PP.asIdeal ∧ s ∉ w.asIdeal := by
      intro PP hPP
      by_contra hcon
      push_neg at hcon
      apply hw PP hPP
      have hle : (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal ≤ w.asIdeal := fun s hs => hcon s hs
      exact HeightOneSpectrum.ext ((HeightOneSpectrum.isMaximal _).eq_of_le w.isPrime.ne_top hle)
    choose! tf htf1 htf2 using hex
    refine ⟨∏ PP ∈ Pg ∪ Q, tf PP, ?_, ?_⟩
    · exact (Submonoid.prod_mem w.asIdeal.primeCompl fun c hc => htf2 c hc : _)
    · have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP) ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
        rw [map_prod]
        exact Ideal.prod_mem_prod fun PP hPP =>
          GlobalTheory.TrOffShift.algebraMap_mem_conjI (D := D) _ _ (htf1 PP hPP)
      exact GlobalTheory.LiftLevel.smul_mem_tens (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP))
        (fun u hu => Submodule.smul_mem_smul hmem hu) hy

end GlobalTheory.LiftLevel.OffTens

end
