import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem stdFst_actO {D : D7} {A WW : HSp D} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E))
    (βA βA' : GL (Fin A.rank) (Lev.EAf D)) (βW βW' : GL (Fin WW.rank) (Lev.EAf D)) (g : GA D A) (h : GA D WW)
    (hfr : ∀ u : WO A WW, IsHalf e u → frMapO A WW βA' βW' (actO A WW g h u) = frMapO A WW βA βW u) (u : WO A WW) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA' βW' (actO A WW g h u) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW u := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  by_cases hu : IsHalf e u
  · rw [hfr u hu]
    have hu' : IsHalf e (actO A WW g h u) := (GlobalTheory.SchrMove.isHalf_actO_iff g h u).2 hu
    by_cases hr : IsIntM (frMapO A WW βA βW u) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW u i j)
    · rw [if_pos ⟨hu', hr⟩, if_pos ⟨hu, hr⟩]
    · rw [if_neg fun hh => hr hh.2, if_neg fun hh => hr hh.2]
  · rw [if_neg fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g h u).1 hh.1), if_neg fun hh => hu hh.1]

theorem move_fst : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g h x y hsg hstg hdg hsh hsth hdh hfr
  classical
  have hI := hY.is
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BotFrames.botBeta G i j)
      (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) ((Y.ω t).toSgn true) := hI.weil t
  have hSA : IsSelfDualC (GlobalTheory.Grid.neg A) Y.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hI.rigW.1
  let g' : GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm g
  have hL : ∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔
      actO (GlobalTheory.Grid.neg A) WW g' h u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) :=
    GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ Y.rA.β Y.rW.β hSA hSW hI.rigA.2.1 hI.rigW.2.1
      g' h hstg hsth
  have hvθ := hI.isVac.2.theta
  have hvL := hI.isVac.2.lat
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hec := (hI.idem t).2
  have h0 : (Y.ω t).toSgn true (g', h) Y.vac =
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) • Y.vac := by
    obtain ⟨ι, P, es, h1, h2, he⟩ := ho
    rw [he] at hec hsg hsh hdg hdh
    have h3 : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := fun a ha b hb => by
      rw [← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 ha, ← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hb, RingHom.map_mul,
        mul_mul_mul_comm, hec, mul_zero]
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvθ hvL es P h1 h2 h3 g' h hsg hsh hL x y hdg hdh
  rw [← isStd_lat_eq hY.std hX.std, ← isStd_lat_eq hY.stdW hX.stdW]
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hI.fst t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have hth := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ hSA hSW (Y.e t) ho.idem
    ho.infPart_eq Y.vac hvθ T' hT'
  have hc : ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' hth hc h0
  have hf := hall _ pm
  have hΦ : (fun u => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW Y.rA.β Y.rW.β (actO (GlobalTheory.Grid.neg A) WW g' h u)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β :=
    funext fun u => stdFst_actO _ _ _ X.rA.β Y.rA.β X.rW.β Y.rW.β g h hfr u
  have e1 : Y.ω t (g⁻¹, h⁻¹) = (Y.ω t).toSgn true (g'⁻¹, h⁻¹) := rfl
  have hf' : Y.f t = ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)⁻¹ •
      (Y.ω t).toSgn true (g', h) (T' (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β)) := by
    rw [hf, ← hΦ]; rfl
  rw [e1, hf', map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel,
    Prod.mk_one_one, map_one, Module.End.one_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.BotFrames

end
