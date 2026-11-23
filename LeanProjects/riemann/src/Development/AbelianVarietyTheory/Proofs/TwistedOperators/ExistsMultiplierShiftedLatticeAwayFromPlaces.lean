import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrOffShift

theorem algebraMap_mem_conjI {D : D7} (I : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.F)
    (h : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ I) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ conjI I := by
  apply Ideal.subset_span
  refine ⟨_, h, ?_⟩
  have h2 := GlobalTheory.Ker.MovLev.bar_algebraMap (D := D) s
  have h3 := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) h2
  simp only [Lev.bar] at h3
  have h4 := IsCMField.coe_ringOfIntegersComplexConj D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s)
  exact h3.symm.trans h4

theorem shift_mult : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  intro D r Pg Q L w hne u hu
  classical
  have hex : ∀ PP ∈ Pg ∪ Q, ∃ s : 𝓞 D.host.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ PP.asIdeal ∧ s ∉ w.asIdeal := by
    intro PP hPP
    by_contra hcon
    push_neg at hcon
    apply hne PP hPP
    have hle : (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal ≤ w.asIdeal := by
      intro s hs
      exact hcon s hs
    exact HeightOneSpectrum.ext
      ((HeightOneSpectrum.isMaximal _).eq_of_le w.isPrime.ne_top hle)
  choose! tf htf1 htf2 using hex
  refine ⟨∏ PP ∈ Pg ∪ Q, tf PP, ?_, ?_⟩
  · have : ∏ PP ∈ Pg ∪ Q, tf PP ∈ w.asIdeal.primeCompl :=
      Submonoid.prod_mem _ (fun c hc => htf2 c hc)
    exact this
  · have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP)
        ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
      rw [map_prod]
      exact Ideal.prod_mem_prod (fun PP hPP => algebraMap_mem_conjI (D := D) _ _ (htf1 PP hPP))
    have h1 := hu _ (algebraMap_mem_conjI (D := D) _ _ hmem)
    exact Submodule.smul_le_right h1

end GlobalTheory.TrOffShift
