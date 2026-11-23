import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.TBLocalW

theorem tb_of_localW : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ),
    LocalSituation.Conclusion4 D HW F →
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h)
        ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie) →
    TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := by
  intro D HW F i r π M0 h0 cB hP hW hF hJ
  obtain ⟨hl2, hJw⟩ := hJ
  intro w hw C hG
  obtain ⟨hIn, hKs, hJC⟩ := hJw w hw
  have hs : Good (D.nbr i w hw).Kw 1 C.LL := hG.good_one hl2 hKs
  have hP1 := hP (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hs
  have hTB := hP1.1
  have hTBe := hP1.2
  have hWs := hW w hw C hs
  have hFa := hF w hw C
  refine ⟨?_, ?_⟩
  · intro Vy _ _ _ _ _ _ _ _ _ _ _ ρy Ly hcy hcrys hjmp p hp hint e₀ he₀ hpe e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat φ hφ
    have hE := GlobalTheory.TBLocal.eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let Yt : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Vy, ρ := ρy, cont := hcy, L := Ly }
    let Y := kerY Yt p e₀ hpe hp hint he₀
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hcjY := cj_sub hFa (GRep.ofLat Yt) (LinearMap.ker p) (ker_stable Yt p hp) ⟨hcrys, hjmp⟩
    have hJY := hJC C hs Y hcjY.1 hcjY.2
    have hWY := hWs Y M0 h0 hcjY.1 hJY.1
    have hJYt := hJC C hs Yt hcrys hjmp
    have hCt := (hWs Yt M0 h0 hcrys hJYt.1).1
    haveI : IsTopologicalRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).LL :=
      inferInstanceAs (IsTopologicalRing ↥C.LL.1)
    haveI : IsDomain (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsDomain ↥(OL C.LL))
    haveI : IsPrincipalIdealRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsPrincipalIdealRing ↥(OL C.LL))
    exact GlobalTheory.TBLocal.tb_part1 (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs)
      Yt p e₀ hpe hp hint he₀ Subtype.val_injective _ hTB e M0 h0 cB VeL hE.1 hE.2 hCt hWY (hJY.2 e he) φ hφ
  · intro e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat
    have hE := GlobalTheory.TBLocal.eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hT := hTBe e VeL hE.1 hE.2
    exact GlobalTheory.TBLocal.tbe_clauses (Br.PD D.loc D.nbr i w hw) Le _ _ hIn e cB hT.2.1 hT.2.2 (hT.1 cB)

end GlobalTheory.TBLocalW
