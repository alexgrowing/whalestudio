import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase

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

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psiword_pf :
    PsiGen → PsiLet → heckeLevelWordBase → LocOk → MLM.MatchLMId → FrFacts → PsiWord := by
  intro hG hPL hW hLO hId hFF hR E _ _ _ n π S T F₀ F i ws
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  have hE := hW E n F.d F.ok (F₀.C.a i) ha (.inr (.inl ()))
  have hB := hW E n F.d F.ok (F₀.C.a i) ha (.inl ())
  have hFx : (F.d.fixL (F₀.C.a i)).Ok F.d.P := (hLO E n F.d F.ok (F₀.C.a i) ha).2.2.1
  have hFe : ((F.d.eL (F₀.C.a i)).mul (F.d.fixL (F₀.C.a i))).Eqv F.d.P (F.d.fixL (F₀.C.a i)) :=
    (hId E n F.d F.ok (F₀.C.a i) ha _ (Or.inr (Or.inl rfl))).2
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := (hFF hR E n π S T F₀ F).2.2.2
  let l : List (BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) :=
    (Sum.inr (F.t₁ i), F.d.fixL (F₀.C.a i)) ::
      (ws.map fun w => List.replicate F.m
          ((Sum.inr (F.β i), F.d.betaL (F₀.C.a i) ha) : BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) ++
        w.map fun p => (gl F i p, locL F.d (F₀.C.a i) ha (lt F p))).flatten
  have e1 : l.map Prod.fst = Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten := by
    simp only [l, bw, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
    rfl
  have e2 : (l.map Prod.snd).foldr LM.mul (F.d.eL (F₀.C.a i)) = prodL F.d (UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw F ws) (F₀.C.a i) := by
    have : l.map Prod.snd = F.d.fixL (F₀.C.a i) :: (UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw F ws).map (locL F.d (F₀.C.a i) ha) := by
      simp only [l, UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
      rfl
    rw [this, prodL, dif_pos ha]
  have hl : ∀ x ∈ l, x.2.Ok F.d.P ∧ ((F.d.eL (F₀.C.a i)).mul x.2).Eqv F.d.P x.2 ∧
      ((∃ c, x.1 = Sum.inl c ∧ x.2 = F.d.eL (F₀.C.a i)) ∨
        ∃ s, x.1 = Sum.inr s ∧ s.ψ = fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) x.2) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hFx, hFe, Or.inr ⟨_, rfl, rfl⟩⟩
    · obtain ⟨y, hy, hxy⟩ := List.mem_flatten.1 hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
      rcases List.mem_append.1 hxy with h | h
      · rw [List.eq_of_mem_replicate h]
        exact ⟨hB.1, hB.2.1, Or.inr ⟨_, rfl, rfl⟩⟩
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 h
        have hp := hW E n F.d F.ok (F₀.C.a i) ha (lt F p)
        refine ⟨hp.1, hp.2.1, ?_⟩
        rcases hPL hR E n π S T F₀ F i p with ⟨c, h1, h2⟩ | ⟨s, h1, h2⟩
        · exact Or.inl ⟨c, h1, h2⟩
        · exact Or.inr ⟨s, h1, h2⟩
  have key := hG E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec hP (F₀.u₁ _) (F₀.u₂ _)
    (F.d.eL (F₀.C.a i)) (F.t₂ i) hE.1 hE.2.1 rfl l hl
  rw [e1, e2] at key
  exact key

end
