import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QQMemAdjAlgCpt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerAnalyticFAllOfTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualOfAnalytic

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

theorem herGenC_herGen {i : Fin (P.r + 1)} {Φ : RadSp P.k P.r z z' π π'}
    (h : HerGenC S P z z' π π' L st l0 D i Φ) : HerGen S P z z' π π' L st l0 D i Φ := by
  induction h with
  | jf F Φ hF hΦ => exact HerGen.jf F Φ hF.1 hΦ
  | slice l w a b Φ hw _ ih => exact HerGen.slice l w a b Φ hw ih
  | waveC l w s Wv Wv' a b Φ hw h1 h2 _ ih => exact HerGen.waveC l w s Wv Wv' a b Φ hw h1 h2 ih
  | waveZ w s Wv Wv' a b Φ hw h1 h2 _ ih => exact HerGen.waveZ w s Wv Wv' a b Φ hw h1 h2 ih

theorem herKc_le_herK (i : Fin (P.r + 1)) : herKc S P z z' π π' L st l0 D i ≤ herK S P z z' π π' L st l0 D i :=
  Submodule.span_le.mpr fun _ hΦ => Submodule.subset_span (herGenC_herGen hΦ)

theorem herKc_sliceIn : SliceIn (S := S) P z z' π π' L st (herKc S P z z' π π' L st l0 D) l0 := by
  intro w hw l x hx
  exact inK_act_span (bTl L l w) (fun a b Φ hΦ => Submodule.subset_span (HerGenC.slice l w a b Φ hw hΦ)) x hx

theorem herKc_waveK : WaveK (S := S) P z z' π π' st (herKc S P z z' π π' L st l0 D) l0 := by
  intro w hw l s Wv Wv' hW hW' x hx
  exact inK_act_span (Vw (mkP Wv Wv') s w)
    (fun a b Φ hΦ => Submodule.subset_span (HerGenC.waveC l w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herKc_waveZ (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')) (hW : multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g))) (x : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herKc S P z z' π π' L st l0 D (Fin.last P.r)) x) :
    InK (herKc S P z z' π π' L st l0 D (Fin.last P.r)) (act (Vw (mkP Wv Wv') s w) x) :=
  inK_act_span (Vw (mkP Wv Wv') s w)
    (fun a b Φ hΦ => Submodule.subset_span (HerGenC.waveZ w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herKc_jf (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π')
    (hΦ : IsRadJF P z z' π π' D F Φ) : Φ ∈ herKc S P z z' π π' L st l0 D 0 :=
  Submodule.subset_span (HerGenC.jf F Φ hF hΦ)

end Classes

def HerCptTopAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    herKc S P z z' π π' L st l0 D (Fin.last P.r) ≤ cptSub P.k P.r z z' π π'

def StepFormCptAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herKc S P z z' π π' L st l0 D) l0 ∧
      FormInt S P z z' π π' μ L st l0 (herKc S P z z' π π' L st l0 D)

theorem stepFormCptAll_of_stepFormAll (h : StepFormAll) : StepFormCptAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  obtain ⟨hSD, hFI⟩ := h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  have hle : ∀ i (x : Ix S → RadSp P.k P.r z z' π π'), InK (herKc S P z z' π π' L st l0 D i) x →
      InK (herK S P z z' π π' L st l0 D i) x := fun i x hx a => herKc_le_herK i (hx a)
  exact ⟨fun w hw l x y hx hy c hc => hSD w hw l x y (hle _ x hx) (hle _ y hy) c hc,
    fun w hw i c hc x y hx hy => hFI w hw i c hc x y (hle _ x hx) (hle _ y hy)⟩

theorem thmPActualCpt_of_herClassesCpt (hHer : HerClassesCpt) (hWC : WaveCommQQAll) : ThmPActualCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  obtain ⟨K, hAdj, hTD, hTT, hSl, hSD, hWK, hFS, hCor, hJ⟩ :=
    hHer Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  refine ⟨K, ?_, hSl, hCor, hJ⟩
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hST := stepTwistFromParts (S := S) P z z' π π' X μ L st K l0 hD Formalism.FourierDecayAlt.P.plane_wave_vector_identity
    (waveSiteAll Wp Wq P z z' π π' X L) (hWC Wp Wq P z z' π π' X μ L st l0 hD) hWK
  exact thmPFromStepsAll Wp Wq S P z z' π π' μ L st K l0 hTI hTD hTT hSl hSD hST hFS

theorem herClassesCpt_of_parts (hT : HerCptTopAll) (hSF : StepFormCptAll) : HerClassesCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' _ _
  obtain ⟨hSD, hFI⟩ := hSF Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  set K := herKc S P z z' π π' L st l0 D with hKdef
  haveI : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hAdj : AdjTop (S := S) P z z' π π' μ L st K l0 :=
    adjTop_cpt P z z' π π' X μ L st K l0 hD (hT Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ')
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD
    Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hXK := xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hTD := topDensNonnegOfKappa Wp Wq S P z z' π π' X μ L st l0 K hD hl1 hl2 hXK
  have hCor := integral_formula_of_steps Wp Wq S P z z' π π' μ L st l0 K hTI hTD herKc_sliceIn hSD
    (topDensMeasAll Wp Wq S P z z' π π' μ L st K)
  have hTT := topTwistDensOfZeta Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt Wp Wq S P z z' π π' X μ L st l0 K hD
  have hFS := formSesqOfInt Wp Wq S P z z' π π' μ L st l0 _ hFI
  refine ⟨K, hAdj, hTD, ?_, herKc_sliceIn, hSD, herKc_waveK, hFS, hCor, ?_⟩
  · intro w hw s Wv Wv' hW hW' x y hx hy c hc
    exact ⟨herKc_waveZ w hw s Wv Wv' hW hW' x hx, hTT w hw s Wv Wv' hW hW' x y hx hy c hc⟩
  · intro F ε hε hF hC hG
    obtain ⟨Φ, hΦ⟩ := radJFExists Wp Wq P z z' π π' D F hD.1 hz hz' hπ hπ' ⟨hF, ε, hε, hG⟩
    exact ⟨Φ, herKc_jf F ⟨⟨hF, ε, hε, hG⟩, hC⟩ Φ hΦ, hΦ⟩

theorem thmPActualCpt_of_parts (hT : HerCptTopAll) (hSF : StepFormCptAll) : ThmPActualCpt :=
  thmPActualCpt_of_herClassesCpt (herClassesCpt_of_parts hT hSF) waveCommQQAll

theorem thmPActualCpt_of_top (hT : HerCptTopAll) (hSF : StepFormAll) : ThmPActualCpt :=
  thmPActualCpt_of_parts hT (stepFormCptAll_of_stepFormAll hSF)

theorem thmPActualCpt_of_thmPActual (h : ThmPActual) : ThmPActualCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  obtain ⟨K, h1, h2, h3, h4⟩ := h Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  exact ⟨K, h1, h2, h3, fun F ε hε hF _ hG => h4 F ε hε hF hG⟩

end Formalism.FourierDecayAlt.P5.HerC
