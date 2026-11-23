import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem SecondG.sAnd_of_largeBase : ∀ (KP : GroupRetwisting.BaseP) (Q Q' R : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.LargeBaseConditionG KP Q R → GroupRetwisting.SecondG KP Q Q' →
    GroupRetwisting.SecondG KP Q (sAnd Q' R) := by
  intro KP Q Q' R hK hR hS
  refine (EvG.inter hR hS).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨S₁r, P₁r, Ar, S₂r, r1, r2, hr⟩, ⟨S₁s, P₁s, As, S₂s, s1, s2, hs⟩⟩ := H
  refine ⟨fun P g F => S₁s P g F ∪ S₁r P g F, fun P g F F₀ => P₁s P g F F₀ ∪ P₁r P g F F₀, As, S₂s, ?_, s2, ?_⟩
  · intro P g F z hz
    rcases Finset.mem_union.1 hz with h | h
    exacts [s1 _ _ _ z h, r1 _ _ _ z h]
  · intro B f T hO hH hP hA hKP hT C W V S N G c hQ hX A S₂ hS₂
    have hH' : Has₂ B (S₁s B.toPre f B.KsC) (S₂s B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨B', f', T', hEnl, hf', hpl, hAv, hS', C', W', V', S', N', G', c', hQ', hTw, hQ''⟩ :=
      hs B f T hO hH' (fun x hx => hP (Finset.mem_union_left _ hx)) hA hKP hT C W V S N G c hQ hX
        (fun l => A l ∪ Ar B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂r P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
        (by
          intro P g Ξ z hz
          rcases Finset.mem_union.1 hz with h | h
          exacts [hS₂ _ _ _ z h, r2 _ _ _ _ _ z h])
    have hP' : B'.toPre = B.toPre := hEnl.1
    have cf : ∀ {α : Type} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {x : Fr P} {y : Fr P'}, P = P' → HEq x y → g P x = g P' y := by
      intro α g P P' x y h hxy
      subst h
      rw [eq_of_heq hxy]
    have hk : B'.KsC = B.KsC := hEnl.KsC_eq
    have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := hEnl.fixedCoefficientField_eq
    have hRc : R K ⟨B', C', W', V', S', N', G'⟩ f' T' c' :=
      hr B' f' T' (hP' ▸ hO)
        ⟨by rw [hk, hl, cf S₁r hP' hf']; exact fun z hz => hH.1 z (Finset.mem_union_right _ hz),
          by rw [hk, hl]; exact fun z hz => hS' z (Finset.mem_union_right _ hz)⟩
        (by rw [hk, hl, cf P₁r hP' hf', hpl]; exact fun x hx => hP (Finset.mem_union_right _ hx))
        (by
          rw [hk, hl, cf Ar hP' hf']
          exact fun w v hv h => hAv w v hv (Finset.mem_union_right _ h))
        (hK.enl B B' f f' hEnl hf' hKP) C' W' V' S' N' G' c' hQ'
    exact ⟨B', f', T', hEnl, hf', hpl, fun w v hv h => hAv w v hv (Finset.mem_union_left _ h),
      fun z hz => hS' z (Finset.mem_union_left _ hz), C', W', V', S', N', G', c', hQ', hTw, hQ'', hRc⟩

end GlobalTheory.Mem.Top.GroupRetwisting
