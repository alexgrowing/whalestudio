import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueFamilyTopRow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamCol
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.MiS GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdForm
set_option maxHeartbeats 2000000 in
theorem clsPinD_of_famCol_of_trueW : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : (I.rec7 l Z).what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.ValidRealPackage W → _root_.GlobalTheory.AdForm.TwStdAlt W → _root_.GlobalTheory.Fam.LeadingReadAt W u f.j f.g.bT → f.RowOK → _root_.GlobalTheory.AdForm.FamilyColumnCondition f → ClsPinD f.t := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W u f hTW hStd hTop hRow hCol
  obtain ⟨c₀, hX, hcol⟩ := hCol
  have hOk := hTW.ok
  have hPins := hTW.pins.some
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_nonzero_jetScale_trueColumns I hOk hPins l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ hX.std hX.inf
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_translates_of_values_frames I hOk hPins l Z (_root_.GlobalTheory.Fam.pk_z W) hX.inf f.j
  have hemb : IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((f.g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) := by
    obtain ⟨UT, ε, hP⟩ := (hcol W.P.A3.A.μ0).2
    exact hP.emb
  refine ⟨realOf u (_root_.GlobalTheory.Fam.pk_z W) f.g s J, GlobalTheory.T.trueColumns_realData_spec I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ s J hX f.j hTop.1 hJ hemb, fun t => ⟨?_, ?_⟩⟩
  · obtain ⟨⟨Ch₀, A, ι, w, hA⟩, -⟩ := hcol t
    exact ⟨_, GlobalTheory.T.kernelPart_laws_of_columnPins I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ s J hX hs hRow.x (_root_.GlobalTheory.Fam.complexLevelStructure W) t (f.row t) (W.P.I.tup t) (f.col t) _ Ch₀ A ι w hA⟩
  · obtain ⟨⟨Ch₀, A, ι, w, hA⟩, UT, ε, hTL⟩ := hcol t
    have hstdC := hTW.std.some
    have key : ∀ a : (I.rec7 l Z).what₂.Tup, _root_.GlobalTheory.Fam.LevelCondition W u a f.g.bT (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) →
        ∃ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := I.rec7 l Z) (u := u) (I.fm l u a) bad)
          (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)),
          I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) ∧
          (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') ∧
          LevG K f.g.bT (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) ∧
          ∀ (ψ : ColT I l u a B.R.m) (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t), ∃ G', ReadsG K eW f.j f.g.bT G' F.1 ∧
            _root_.GlobalTheory.Fam.tailCoefficient W u f.j f.g.bT a ψ F.1 = (I.per l u a).Ptil ψ G' := by
      intro a hL
      by_cases h0 : a = I.mu0
      · subst h0
        have hon := GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ hX f.j hTop.1 (_root_.GlobalTheory.Fam.complexLevelStructure W) t I.mu0 _ (W.R.T.cols.forms u).clsP.toG
          (W.R.T.cols.forms u).valP.eW (hstdC u).what₂ (hstdC u).eW hTop.2.1 (hL.1 rfl)
        refine ⟨_, (W.R.T.cols.forms u).clsP.toG, (W.R.T.cols.forms u).valP.eW, (hstdC u).what₂, (hstdC u).eW, hL.1 rfl, ?_⟩
        intro ψ F
        have hex : ∃ G, _root_.GlobalTheory.Fam.ReadsCoefficients W u f.j f.g.bT I.mu0 G F.1 := by
          obtain ⟨G', hG'⟩ := hon F
          refine ⟨(I.rec7 l Z).eMt u G', fun h => ?_, fun h => absurd rfl h⟩
          have e : ((I.rec7 l Z).eMt u).symm (h ▸ ((I.rec7 l Z).eMt u) G') = G' := ((I.rec7 l Z).eMt u).symm_apply_apply G'
          first
            | (rw [e]; exact hG')
            | exact e ▸ hG'
            | exact (congrArg (fun G => ReadsG (W.R.T.cols.forms u).clsP.toG (W.R.T.cols.forms u).valP.eW f.j f.g.bT G F.1) e).mpr hG'
        refine ⟨_, hex.choose_spec.1 rfl, ?_⟩
        unfold _root_.GlobalTheory.Fam.tailCoefficient
        rw [dif_pos hex]
        split
        · rfl
        · next h => exact absurd rfl h
      · obtain ⟨l0, t', e, hh, hst⟩ := hStd
        obtain ⟨-, -, hP⟩ := hst
        cases ex
        dsimp only at e
        subst e
        have hh' := eq_of_heq hh
        subst hh'
        have hon := GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ hX f.j hTop.1 (_root_.GlobalTheory.Fam.complexLevelStructure W) t a _ (W.R.T.tw.pt.cls u a h0)
          (W.R.T.tw.pt.val u a h0).eW (hP.what₂ u a h0) (hP.eW u a h0) hTop.2.1 (hL.2 h0)
        refine ⟨_, W.R.T.tw.pt.cls u a h0, (W.R.T.tw.pt.val u a h0).eW, hP.what₂ u a h0, hP.eW u a h0, hL.2 h0, ?_⟩
        intro ψ F
        have hex : ∃ G, _root_.GlobalTheory.Fam.ReadsCoefficients W u f.j f.g.bT a G F.1 := by
          obtain ⟨G', hG'⟩ := hon F
          refine ⟨(I.rec7 l Z).eMtTw u a G', fun h => absurd h h0, fun h => ?_⟩
          have e := ((I.rec7 l Z).eMtTw u a).symm_apply_apply G'
          first
            | (rw [e]; exact hG')
            | exact e ▸ hG'
            | exact (congrArg (fun G => ReadsG (W.R.T.tw.pt.cls u a h0) (W.R.T.tw.pt.val u a h0).eW f.j f.g.bT G F.1) e).mpr hG'
        refine ⟨_, hex.choose_spec.2 h0, ?_⟩
        unfold _root_.GlobalTheory.Fam.tailCoefficient
        rw [dif_pos hex]
        split
        · next h => exact absurd h h0
        · rfl
    obtain ⟨bad, K, eW, h1, h2, h3, h4⟩ := key _ (hTop.2.2 t).1
    exact GlobalTheory.T.exists_lastPeriod_classData_of_lastStep I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ s J hX f.j hTop.1 hJ (_root_.GlobalTheory.Fam.complexLevelStructure W) t (f.row t) (W.P.I.tup t) (f.col t) _ Ch₀ A ι w hA UT ε hTL bad K eW h1 h2 hTop.2.1 h3 h4
end GlobalTheory.AdForm
end
