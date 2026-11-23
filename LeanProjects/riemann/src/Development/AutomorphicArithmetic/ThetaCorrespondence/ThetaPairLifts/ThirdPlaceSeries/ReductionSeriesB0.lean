import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB0Statement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsGridAtMember
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalExOfCgTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SecondStepStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
open Formalism.L2.TwC in
theorem pointwise_alt_alt (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hSer : SerN) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x)
    (G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩)
    (hF : GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x))) (hOk : (GlobalTheory.BigTop.Fun.lamOf G).Ok)
    (hC : (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x) (hq : (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x)) :
    ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x') ∧ ListSt cDep x' := by
  have hgal : GalEx (Dof x) :=
    _root_.GlobalTheory.HeightCounting.galEx_of_cgTrue_alt hL hPr.what₂.fin hPr.what₂.gal (Dof x) l.a.A.wdT ⟨l.a.cg⟩
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb (Dof x)
  obtain ⟨c0f, hf⟩ := _root_.GlobalTheory.T.row_cusp_multiplicity_input_alt hPr.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A l.rat.S l.rat.In (lowAll (Dof x)) l.Pq
    l.mt.M _ (QOf P) l.mt.mt l.Pq_over hgal l.cusp hcheb l.a.elem.star l.a.elem.int l.a.elem.split
  have hJ := fun (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ↥(Dof x).LL0))
      (hv : ((p : ℕ) : 𝓞 ↥(Dof x).LL0) ∈ v.asIdeal) => Formalism.BasicNotions.Examples₂.LB.exists_embAt (l := p) v hv
  obtain ⟨c0r, hr⟩ := GlobalTheory.T.exists_twistRings_characters_classGroups hPr.what₂.art (Dof x) (cfOf x) (fun p _ v hv => (hJ p v hv).choose)
    (fun p _ v hv y => (hJ p v hv).choose_spec y) l.a.val l.a.elem.star l.a.elem.int
  let b0 : Big (Dof x) := fun p _ j =>
    ⟨(c0f p j).1 ⊔ (c0r p j).1, by haveI := (c0f p j).2; haveI := (c0r p j).2; infer_instance⟩
  obtain ⟨Sx, hSx1, hSx2, hSx3⟩ := exists_Sx (Dof x)
  obtain ⟨T', Sp, -⟩ := hr b0 b0 Sx (fun p _ j => le_sup_right)
  have hSbSx : l.rat.In.Sb ⊆ Sx := l.rat.rat.Sb_le.subset hSx1
  obtain ⟨F, ex, h0, hfg, hsb⟩ := hf b0 b0 Sx T' Sp (fun p _ j => le_sup_left) hSbSx hSx3 hSx1
  have hSxS0 : ∀ i, ∀ Q ∈ Sx, Q ∈ T'.S0 i := fun i Q hQ => by
    have h := Sp.ringSpec_excludedPlaces_eq i
    have : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := by
      rw [h]; exact Or.inr (Finset.mem_coe.2 hQ)
    exact Finset.mem_coe.1 this
  have hratio : ∀ i, ∀ y ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)),
      ∀ z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)), ‖y‖ ≤ ‖z‖ →
        y / z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)) := fun i => by
    have h := GlobalTheory.CycClosure.exists_cyclotomic_integers (T'.l i) (Sp.K0 i) (Sp.Lw i) 0
    have h0 : Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) ⊔ muK (T'.l i) 0 = Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) := by
      rw [h.snd.2.2.2.2.1, sup_bot_eq]
    rw [h0] at h
    exact h.snd.2.2.2.1
  choose iC hiC using fun i => GlobalTheory.Mem.Df.exists_iC_of_clC (T'.l i) (T'.O i) _ (Sp.eO i) (hratio i)
  obtain ⟨L, hLam⟩ := GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings hPr.what₂.cheb hPr.what₂.art hSer.ratio (Dof x) l.a.A.bare (cfOf x) l.a.A.row
    (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ b0 b0 Sx T' Sp (GlobalTheory.BigTop.Fun.lamOf G) hC hOk
    (GlobalTheory.BigTop.Fun.lamOf_teich G) l.a.val (fun a => hF.values (a.1 + 1) (by omega) a.2)
    (fun i Q hQ => by
      obtain ⟨p, hp, hQp⟩ := GlobalTheory.T.conductor_primes_in_low_set (Dof x) _ hOk hq Q hQ
      exact hSxS0 i Q (Finset.mem_coe.1 (hSx1 p hp hQp)))
  obtain ⟨htie, hside⟩ := hLam F
  obtain ⟨th0⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F (TwL.empty T')) ex
    (fun i => ⟨iC i, hiC i⟩) hfg
  obtain ⟨th1⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F L) { ex with }
    (fun i => ⟨iC i, hiC i⟩) hfg
  have hB := hside ex h0 th0 (hsb th0) th1
  refine _root_.GlobalTheory.T.side_data_over_set_levels_alt hL cDep x l ⟨T'.ntw l.a.A.bare F L, { ex with }, h0, th1, Sp.br, Sp.br_ind⟩ hB
    (fun i => hSbSx.trans fun Q hQ => hSxS0 i Q hQ) (fun i Q hQ => ?_) G hF hOk hC hq htie
  have h := Sp.ringSpec_excludedPlaces_eq i
  have hQ' : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := Finset.mem_coe.2 hQ
  rw [h] at hQ'
  simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_coe] at hQ'
  rcases hQ' with (((h1 | ⟨k, h1⟩) | h1) | h1) | h1
  · exact ⟨_, Finset.mem_insert_self _ _, h1⟩
  · refine ⟨(Dof x).host.g k, Finset.mem_insert_of_mem ?_, h1⟩
    fin_cases k <;> simp [lowAll]
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · obtain ⟨p, hp, hQp⟩ := hSx2 Q h1
    exact ⟨p, Finset.mem_insert_of_mem hp, hQp⟩
theorem settings_forms_exist_list_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep := by
  intro hPr hSer hL cDep
  exact (_root_.GlobalTheory.T.exists_lam_grid_fieldHas_at_member hPr cDep).trans (StepW.of_all fun K B f T w _ _ h P x l => by
    obtain ⟨G, hF, hOk, hC, hq⟩ := h P x
    exact _root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.pointwise_alt_alt hPr hSer hL cDep x l G hF hOk hC hq)
end GlobalTheory.HeightCounting.Up.PointwiseSettings
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.settingsFormsExistList_of_inputs_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.settings_forms_exist_list_of_published_inputs | exact _root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.settings_forms_exist_list_of_published_inputs | (intros; apply _root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.settings_forms_exist_list_of_published_inputs <;> assumption)
end
end
