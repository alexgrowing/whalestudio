import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftOfEachRow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitLiftOfLiftParam

noncomputable section

namespace GlobalTheory.Proof.SplitPlaceGoodSignature

open NumberField Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem isSplitPl_of_not_isConjPl (w : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E))
    (h : ¬ IsConjPl H w w) : IsSplitPl H w := by
  by_contra hs
  apply h
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  have hc : ∀ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y = c x := fun x y hy =>
    RingOfIntegers.ext hy
  have hle : w.asIdeal ≤ w.asIdeal.comap c := by
    intro x hx
    by_contra hx'
    exact hs ⟨x, hx, fun y hy => by rw [hc x y hy]; exact hx'⟩
  have heq : w.asIdeal = w.asIdeal.comap c :=
    w.isMaximal.eq_of_le (Ideal.comap_ne_top c w.isPrime.ne_top) hle
  intro x y hy
  rw [hc x y hy, ← Ideal.mem_comap, ← heq]

variable (N : NData R H what₂) (A : NAut N)

theorem typePlSplit : TypePlSplit N A := fun k v =>
  isSplitPl_of_not_isConjPl _ (A.plGw_nconj k v v)

theorem isoLoc_lift (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by
  rw [Check.iso_char N A hL, Check.iso_append]
  rfl

theorem goodRow_iff_goodSig {i : N.Loc} {σ : what₂.FT} {Sig : List (Part A.CG)}
    (h : ∀ w, IsSplitPl H w → isoLoc N A Sig w = A.locW i σ w) :
    N.goodRow σ ↔ goodSig N A Sig := by
  have hl : ∀ k, (fun v => A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))) = N.lab k σ := by
    intro k
    funext v
    rw [h _ (typePlSplit N A k v), A.lab_loc i k σ v]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [hl k]

theorem isoLoc_eq_of_hasParamX (hL : ParamLaws N A) {i : N.Loc} (hloc : LocOfPt N A i) {x : N.X i}
    {Sig Sig' : List (Part A.CG)} (h : HasParamX N A i x Sig) (h' : HasParamX N A i x Sig')
    (w : PlE H) (hw : IsSplitPl H w) : isoLoc N A Sig w = isoLoc N A Sig' w := by
  obtain ⟨P, hP, hB⟩ := h
  obtain ⟨P', hP', hB'⟩ := h'
  have e := hloc P P' x hP hP' w hw
  rw [← hB.2.2.2.1 w hw, ← hB'.2.2.2.1 w hw, isoLoc_lift N A hL, isoLoc_lift N A hL] at e
  exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)

theorem goodPart_of_lifts (i : N.Loc) (h1 : ThetaOne N A) (hL : ParamLaws N A)
    (hlift : LiftParam N A i) (hpt : PtLocal N A i) (hloc : LocOfPt N A i) : GoodPart N A i := by
  unfold GoodPart goodPartM
  apply le_antisymm
  · refine iSup₂_le fun σ hσ => ?_
    obtain ⟨hg, Sig₀, hW₀, x₀, hx₀⟩ := hσ
    by_cases hb : what₂.isot (N.j i) σ = ⊥
    · rw [hb]; exact bot_le
    obtain ⟨P, hP⟩ := h1 i σ hb
    obtain ⟨Sig, hW, hB⟩ := hlift σ P hP
    obtain ⟨y, hy⟩ := hpt P x₀ fun w hw => by
      obtain ⟨p, hp, hp'⟩ := hx₀ w hw
      refine ⟨p, ?_, hp'⟩
      rw [hp, ← hB.2.2.2.1 w hw.1, isoLoc_lift N A hL, isoLoc_lift N A hL, hW₀.2.2 w hw.1,
        hW.2.2 w hw.1]
    have hX : HasParamX N A i y Sig := ⟨P, hy, hB⟩
    have hZ : y ∈ ZgoodN N A i := by
      refine ⟨⟨P, hy, _, hB, ?_⟩, Sig, hX, (goodRow_iff_goodSig N A hW.2.2).1 hg⟩
      exact List.mem_map.2 ⟨muPart N A i, by simp, rfl⟩
    refine le_iSup₂_of_le y hZ (le_iSup₂_of_le Sig hX ?_)
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | HasParamW N A i σ Sig}) =>
      what₂.isot (N.j i) σ) σ hW le_rfl
  · refine iSup₂_le fun x hx => iSup₂_le fun Sig hX => ?_
    unfold MjSig
    refine iSup₂_le fun σ hW => ?_
    obtain ⟨-, Sig', hX', hg⟩ := hx
    have hgood : N.goodRow σ := (goodRow_iff_goodSig N A (i := i) fun w hw =>
      (isoLoc_eq_of_hasParamX N A hL hloc hX' hX w hw).trans (hW.2.2 w hw)).2 hg
    have hat : AtM N A i σ := by
      obtain ⟨P, hP, hB⟩ := hX
      refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
      rw [hB.2.2.2.1 w hw.1]
      exact A.pt_loc i P x hP w hw
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | N.goodRow σ ∧ AtM N A i σ}) =>
      what₂.isot (N.j i) σ) σ ⟨hgood, hat⟩ le_rfl

end GlobalTheory.Proof.SplitPlaceGoodSignature
