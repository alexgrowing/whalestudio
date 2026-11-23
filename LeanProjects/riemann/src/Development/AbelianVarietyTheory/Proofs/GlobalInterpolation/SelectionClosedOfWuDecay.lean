import Mathlib
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AdmissibilityClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GapClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Top.selection_closed_of_wu_decay : ∀ (𝒜 : FamClass)
    (sel : Formalism.L2.TSel 𝒜)
    (selS : SelS 𝒜 sel)
    (selP : BaseLevelCompatibleSelection 𝒜 sel)
    (selDH : SelDH 𝒜 sel)
    (selC : ColumnCompatibleSelection 𝒜 sel selP)
    (selB : SelB 𝒜 sel selS selP selDH selC)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (selJ : Formalism.L2.SG.JoinSISel.SelJ 𝒜 sel selS selP selDH selC (selKOf selB) (selIOf selB))
    (jOn : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.L2.SG.JoinSISel.BaseVectorImageFull (Fm.D x i))
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, RowsAtSel sel (selIOf selB) (fun Fm hc x hx h i C CH => Formalism.L2.Top4Wire2.DefRowsF (selIOf selB) Fm hc x hx h i C CH) (OneMapOf selB)
        Fm (d3_a hc) CH), Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm := by
  intro 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have jGap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm,
      Formalism.L2.Top4.EvSel sel Fm (d3_a hc) fun x _ _ i => Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
    (Formalism.L2.SG.GapClosed.gapEv_closed_of (D3 3 𝒜) fun _ hc => hc.2.2.1).imp fun Fm _ _ h hc => by
      obtain ⟨y, hy⟩ := h hc
      exact ⟨y, fun x _ _ hxy i => hy x hxy i⟩
  have hM : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, EvSel (fun Fm hc => sel Fm (d3_a hc)) Fm hc fun x hx h i =>
      Formalism.L2.SG.JoinSISel.MIAt2 ((selIOf selB) Fm (d3_a hc) x hx h i) :=
    rRows.imp fun Fm CH _ h hc => by
      obtain ⟨C, _, x0, H⟩ := h hc
      exact ⟨x0, fun x hx hs hx0 i => (H x hx hs hx0 i).1.miStar⟩
  have hFX := Formalism.L2.SG.JoinSISel.finXRow_of_gap (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
    (selS := fun Fm hc => selS Fm (d3_a hc)) (Formalism.L2.SG.Pf.finXC_of hWu hRF)
    jGap
  have hC5 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm :=
    Formalism.L2.SG.JoinSISel.closed_complementFiveFamily_of_evSel_imageFull (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
      (selS := fun Fm hc => selS Fm (d3_a hc)) (selP := fun Fm hc => selP Fm (d3_a hc)) (selDH := fun Fm hc => selDH Fm (d3_a hc))
      (selC := fun Fm hc => selC Fm (d3_a hc)) (selK := fun Fm hc => (selKOf selB) Fm (d3_a hc)) (selI := fun Fm hc => (selIOf selB) Fm (d3_a hc))
      (fun Fm hc => selJ Fm (d3_a hc)) hM hFX jOn
  exact hC5
