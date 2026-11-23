import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.Lt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.PLocWord
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFrameOk
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.MatchAll

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

namespace PWordId2

section Frame

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)

theorem wb_wd_ok {B : Block E} (t₀ : PT B) (h₀ : t₀.Ok) : ∀ w : List (BGen B), (∀ g ∈ w, g.Ok) → (BGen.wd w t₀).Ok
  | [], _ => h₀
  | .inl _ :: w, h => wb_wd_ok t₀ h₀ w fun g hg => h g (List.mem_cons_of_mem _ hg)
  | .inr s :: w, h => (BlockFiniteConvolution.blkOp₀ E B s _ (h _ List.mem_cons_self)
      (wb_wd_ok t₀ h₀ w fun g hg => h g (List.mem_cons_of_mem _ hg))).2.2.1

theorem wb_adj_ok {B : Block E} : ∀ g : BGen B, g.Ok → g.adj.Ok
  | .inl _, _ => trivial
  | .inr s, h => (BlockFiniteConvolution.blkOp₀ E B s s h h).2.2.2.2.1

theorem wb_eL_adj (d : LocData E n) {a : ℕ} (ha : a ≤ n) : (d.eL a).adj.Eqv d.P (d.eL a) :=
  ⟨fun w _ => congrFun (LocComm.adj_m d (ha := ha) (Or.inl rfl)) w, fun _ _ => LocComm.lfStar_idem _,
    funext fun _ => LocComm.lfStar_idem _⟩

theorem wb_letter (i : F₀.C.ι) (p : F.Γ × Bool) :
    (∀ s, gl F i p = Sum.inr s → s.ψ = fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) (locL F.d _ (F₀.C.le i) (lt F p))) ∧
      ∀ c, gl F i p = Sum.inl c → locL F.d _ (F₀.C.le i) (lt F p) = F.d.eL _ := by
  have A := BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec (FrameOk.wirtinger_sub F)
  have O := (BlockFiniteConvolution.locOk₀ E n F.d F.ok _ (F₀.C.le i)).2.2.2
  have he : adjF (F.ψ i (F.d.eL _)) = fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) (F.d.eL _) :=
    (A _ _ (O _ (Or.inl rfl)) (O _ (Or.inl rfl))).2.2.2.2.trans (fm_congr _ (wb_eL_adj F.d (F₀.C.le i)))
  obtain ⟨x | x | x, b⟩ := p
  · refine ⟨fun s hs => ?_, fun _ _ => rfl⟩
    cases b
    · obtain rfl : F.t₀ i = s := Sum.inr.inj hs
      rfl
    · obtain rfl : (F.t₀ i).adj = s := Sum.inr.inj hs
      exact he
  · refine ⟨fun s hs => ?_, fun _ _ => rfl⟩
    by_cases h : i = x.1
    · have e : F.g (.inr (.inl x)) i = .inr (F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := if_pos h
      unfold gl at hs
      rw [e] at hs
      cases b
      · obtain rfl := Sum.inr.inj hs
        rfl
      · obtain rfl := Sum.inr.inj hs
        exact he
    · have e : F.g (.inr (.inl x)) i = .inl (F.dval x) := if_neg h
      unfold gl at hs
      rw [e] at hs
      cases b <;> exact absurd hs Sum.inl_ne_inr
  · cases b
    · refine ⟨fun s hs => ?_, fun c hc => absurd hc Sum.inr_ne_inl⟩
      obtain rfl := Sum.inr.inj hs
      rfl
    · refine ⟨fun s hs => ?_, fun c hc => absurd hc Sum.inr_ne_inl⟩
      obtain rfl := Sum.inr.inj hs
      have o := O _ (Or.inr ⟨x.1.1, x.2.1, x.2.2, x.1.2.2, rfl⟩)
      exact (A _ _ o o).2.2.2.2

theorem blk_eq (h : LocWord) (hF : F.Struct) (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))) :
    (prodL F.d (ls F ws) (F₀.C.a i)).Ok F.d.P ∧ (tw F i ws).Ok ∧
    (tw F i ws).ψ = rt (F₀.u₁ _) (F₀.u₂ _) (fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) (prodL F.d (ls F ws) (F₀.C.a i))) ∧
    trM (tw F i ws).Φ (MM F i) = (F.B i).vol⁻¹ • adel F₀.Sec (F₀.u₁ (F₀.C.a i)) (F₀.u₂ (F₀.C.a i))
      ((tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb) ((prodL F.d (ls F ws) (F₀.C.a i)).tr F.d.P F.d.one)
      (prodL F.d (ls F ws) (F₀.C.a i)).t := by

  have O := BlockFiniteConvolution.locOk₀ E n F.d F.ok _ (F₀.C.le i)
  have L := (h E n F.d F.ok _ (F₀.C.le i) [Sum.inl ()] 0 rfl).1
  let prs : List (BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) := (Sum.inr (F.t₁ i), F.d.fixL _) ::
    (ws.map fun w => List.replicate F.m (Sum.inr (F.β i), F.d.betaL _ (F₀.C.le i)) ++
      w.map fun p => (gl F i p, locL F.d _ (F₀.C.le i) (lt F p))).flatten
  have e1 : prs.map Prod.fst = Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten := by
    simp only [prs, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
    rfl
  have e2 : prs.map Prod.snd = F.d.fixL _ :: (ls F ws).map (locL F.d _ (F₀.C.le i)) := by
    simp only [prs, ls, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
    rfl
  have e3 : prodL F.d (ls F ws) (F₀.C.a i) = (prs.map Prod.snd).foldr LM.mul (F.d.eL _) := by
    rw [e2, prodL, dif_pos (F₀.C.le i)]
  have e4 : tw F i ws = BGen.wd (prs.map Prod.fst) (F.t₂ i) := by rw [e1]; rfl
  have R := adelRep2 (S := F₀.Sec) (B := F.B i) (Equiv.refl _) F₀.hSec (FrameOk.wirtinger_sub F) (fun w _ => O.1 w) (F₀.u₁ _) (F₀.u₂ _)
    (F₀.A i).Ta (F₀.A i).Tb F.d.one (F.d.eL _) (F.d.eL _) (F.t₂ i) (L (.inr (.inl ()))).1 (L (.inr (.inl ()))).1
    (L (.inr (.inl ()))).2.1 rfl prs (by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨O.2.2.1, (MatchAll.matchLMId E n F.d F.ok _ (F₀.C.le i) _ (Or.inr (Or.inl rfl))).2,
          fun s hs => by obtain rfl := Sum.inr.inj hs; rfl, fun c hc => absurd hc Sum.inr_ne_inl⟩
      obtain ⟨l, hl, hp⟩ := List.mem_flatten.1 hp
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
      rcases List.mem_append.1 hp with hp | hp
      · obtain rfl := List.eq_of_mem_replicate hp
        exact ⟨(L (.inl ())).1, (L (.inl ())).2.1, fun s hs => by obtain rfl := Sum.inr.inj hs; rfl,
          fun c hc => absurd hc Sum.inr_ne_inl⟩
      · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
        exact ⟨(L _).1, (L _).2.1, wb_letter F i q⟩)
  refine ⟨e3 ▸ R.1, wb_wd_ok _ (hF.tok i).2 _ fun g hg => ?_, ?_, ?_⟩
  · rcases List.mem_cons.1 hg with rfl | hg
    · exact (hF.tok i).1
    obtain ⟨l, hl, hg⟩ := List.mem_flatten.1 hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
    rcases List.mem_append.1 hg with hg | hg
    · obtain rfl := List.eq_of_mem_replicate hg
      exact hF.βok i
    · obtain ⟨⟨x, b⟩, -, rfl⟩ := List.mem_map.1 hg
      cases b
      · exact hF.ok x i
      · exact wb_adj_ok _ (hF.ok x i)
  · rw [e3, e4]; exact R.2.1
  · rw [e3, e4]; exact R.2.2

end Frame

end PWordId2

end PositivityTheory.Rg.BcB.F.B3

end
