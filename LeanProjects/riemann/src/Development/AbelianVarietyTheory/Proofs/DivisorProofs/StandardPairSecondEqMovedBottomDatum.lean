import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFrames

theorem isThetaAt_stdSnd_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g' : GA D A') (h : GA D WW) (x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
      frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u) →
    IsThetaAt W.ψ (symplO A' WW) (heisO W.ψ A' WW) (cA D (Y.e t))
      (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 Y.vac'
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t)
        A.rank A' WW X.rA'.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) • Y.ω' t (g'⁻¹, h⁻¹) (Y.f' t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g' h x' y hS1 hSt1 hD1 hS2 hSt2 hD2 hfr
  have hi := hY.is
  have hW : IsWeilDatumO W.ψ A' WW (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) (Y.ω' t) :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hi.weil' t)
  have hSA : IsSelfDualC A' Y.rA'.Λ := hi.rigA'.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hi.rigW.1
  have hFA : Formalism.L2.DIV.IsFrame Y.rA'.β Y.rA'.Λ := hi.rigA'.2.1
  have hFW : Formalism.L2.DIV.IsFrame Y.rW.β Y.rW.Λ := hi.rigW.2.1
  have eA : X.rA'.Λ = Y.rA'.Λ := isStd_lat_eq hX.std' hY.std'
  have eW : X.rW.Λ = Y.rW.Λ := isStd_lat_eq hX.stdW hY.stdW
  rw [eA, eW]
  have hL := GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D A' WW Y.rA'.Λ Y.rW.Λ Y.rA'.β Y.rW.β hSA hSW hFA hFW g' h hSt1 hSt2
  have hvac := hi.isVac'
  have hIS := hi.idem t
  obtain ⟨ι, P, es, hsp, horth, hsum⟩ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS
  have hc0 : Y.e t * cA D (Y.e t) = 0 := hIS.2
  have hes : ∀ k ∈ P, es k * Y.e t = es k := by
    intro k hk
    rw [hsum, Finset.mul_sum, Finset.sum_eq_single_of_mem k hk (fun b hb hne => horth k hk b hb hne)]
    exact (hsp k hk).1
  have hecs : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := by
    intro a ha b hb
    have h2 : cA D (es b) * cA D (Y.e t) = cA D (es b) := by rw [← map_mul, hes b hb]
    rw [← hes a ha, ← h2]
    calc es a * Y.e t * (cA D (es b) * cA D (Y.e t)) = es a * cA D (es b) * (Y.e t * cA D (Y.e t)) := by ring
      _ = 0 := by rw [hc0, mul_zero]
  have h0 : Y.ω' t (g', h) Y.vac' =
      ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) • Y.vac' := by
    rw [hsum] at hS1 hS2 hD1 hD2
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvac.2.theta hvac.2.lat es P hsp horth hecs g' h hS1 hS2 hL x' y hD1 hD2
  have hos := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hc : ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have hΦ : (LinearMap.funLeft ℂ ℂ (actO A' WW g' h))
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW Y.rA'.β Y.rW.β) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW X.rA'.β X.rW.β := by
    funext u
    rw [LinearMap.funLeft_apply]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
    by_cases hu : IsHalf (cA D (Y.e t)) u
    · have hd : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) =
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW X.rA'.β X.rW.β u := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
        rw [hfr u hu]
      rw [hd, GlobalTheory.SchrMove.isHalf_actO_iff]
    · rw [if_neg, if_neg]
      · exact fun hh => hu hh.1
      · exact fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g' h u).1 hh.1)
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hi.snd t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std A' WW Y.rA'.Λ Y.rW.Λ hSA hSW (cA D (Y.e t)) hos.idem
    hos.infPart_eq Y.vac' hvac.2.theta T' hT'
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' th1 hc h0
  have hf' := hall _ pm
  have omm : ∀ p q (F : WO A' WW → ℂ), Y.ω' t p (Y.ω' t q F) = Y.ω' t (p * q) F := fun p q F => by
    rw [map_mul]; rfl
  show _ = T' _
  rw [← hΦ, hf']
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]
  rfl

end GlobalTheory.BotFrames
