import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedStateTransportHeqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2TransportStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lb1OfRestagingHostsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2ExtensionStatement

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem mvB_carry : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P), StrictHenselianAcyclic hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', LI hL x' → SameGal (Dof x) (Dof x') → ∃ x'' : St P', Nonempty (SeriesLevel hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  intro hPr hSer hL
  refine Step.of_evG (((evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).inter (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev)).imp
    fun K _ _ _ _ H B' f' T' hO hKP hF _ w' hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG => ?_)
  have hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV :=
    fun X hX => ⟨(H.1 X hX).1, (H.2 X hX).2⟩
  obtain ⟨N, ι, e, hN⟩ := GlobalTheory.T.enlarged_base_lb2_transport hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG
  obtain ⟨x'', l'', ho, hlev, hrow, hPq, hRS, hSb, hhL, heig, hθ⟩ := GlobalTheory.T.twisted_state_transport_heq hL x' l' N
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]
    rfl
  refine ⟨x'', GlobalTheory.T.lb1_of_restaging_hosts hPr hSer hL hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev
    hrow hPq hRS hSb hhL heig hθ, ?_, GlobalTheory.T.enlarged_base_lb2_extension hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e
    hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ⟩
  rw [hD]
  exact hN.carried

end GlobalTheory.HeightCounting.Up

end
