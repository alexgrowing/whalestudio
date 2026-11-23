import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psilet_pf :
    FmAlg → LocOk → FrFacts → PsiLet := by
  intro hA hO hF hR E _ _ _ n π S T F₀ F i p
  obtain ⟨g, b⟩ := p
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := (hF hR E n π S T F₀ F).2.2.2
  have hok : ∀ L, F.d.IsGen (F₀.C.a i) (F₀.C.le i) L → L.Ok F.d.P := fun L hL =>
    (hO E n F.d F.ok (F₀.C.a i) (F₀.C.le i)).2.2.2 L hL
  have hadj : ∀ L, F.d.IsGen (F₀.C.a i) (F₀.C.le i) L → adjF (F.ψ i L) = F.ψ i L.adj := fun L hL =>
    (hA E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec hP L L (hok L hL) (hok L hL)).2.2.2.2
  have heL : (F.d.eL (F₀.C.a i)).adj = F.d.eL (F₀.C.a i) := by
    have hm := LocComm.adj_m F.d (a := F₀.C.a i) (ha := F₀.C.le i) (L := F.d.eL (F₀.C.a i)) (Or.inl rfl)
    have hs : (F.d.eL (F₀.C.a i)).adj.s = (F.d.eL (F₀.C.a i)).s := by
      funext w
      exact LocComm.lfStar_idem _
    have ht : (F.d.eL (F₀.C.a i)).adj.t = (F.d.eL (F₀.C.a i)).t := by
      funext w
      exact LocComm.lfStar_idem _
    cases h : F.d.eL (F₀.C.a i) with
    | mk m s t =>
      rw [h] at hm hs ht
      simp only [LM.adj] at hm hs ht ⊢
      rw [LM.mk.injEq]
      exact ⟨hm, hs, ht⟩
  have heψ : adjF (F.ψ i (F.d.eL (F₀.C.a i))) = F.ψ i (F.d.eL (F₀.C.a i)) := by
    rw [hadj _ (Or.inl rfl), heL]
  rcases g with _ | x | x
  · refine Or.inr ?_
    cases b
    · exact ⟨F.t₀ i, rfl, rfl⟩
    · exact ⟨(F.t₀ i).adj, rfl, heψ⟩
  · by_cases hi : i = x.1
    · refine Or.inr ?_
      cases b
      · exact ⟨F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2, by simp [gl, RunFrame.g, hi], rfl⟩
      · refine ⟨(F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).adj, by simp [gl, RunFrame.g, hi, BGen.adj], heψ⟩
    · refine Or.inl ?_
      cases b
      · exact ⟨F.dval x, by simp [gl, RunFrame.g, hi], rfl⟩
      · exact ⟨starRingEnd ℂ (F.dval x), by simp [gl, RunFrame.g, hi, BGen.adj], rfl⟩
  · refine Or.inr ?_
    cases b
    · exact ⟨F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2), rfl, by simp [lt, locL]; rfl⟩
    · exact ⟨(F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)).adj, rfl,
        (hadj _ (Or.inr ⟨x.1.1, x.2.1, x.2.2, x.1.2.2, rfl⟩)).trans (by simp [lt, locL])⟩

end
