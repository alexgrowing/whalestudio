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

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit}
  {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)

private theorem lw_cons (w : List (F.Γ × Bool)) (ws : List (List (F.Γ × Bool))) :
    lw F (w :: ws) = (List.replicate F.m (Sum.inl ()) ++ w.map (lt F)) ++ lw F ws := by
  simp [UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw]

private theorem count_lt (w : List (F.Γ × Bool)) : (w.map (lt F)).countP Sum.isLeft = 0 := by
  rw [List.countP_eq_zero]
  intro a ha
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
  rcases p with ⟨(_ | _ | x), b⟩ <;> simp [lt]

private theorem count_lw (ws : List (List (F.Γ × Bool))) :
    (lw F ws).countP Sum.isLeft = F.m * ws.length := by
  induction ws with
  | nil => simp [UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw]
  | cons w ws ih =>
    rw [lw_cons, List.countP_append, List.countP_append, ih, count_lt, List.countP_replicate]
    simp <;> ring

private theorem atPlace_append (w : Pl E) (l₁ l₂ : List (LL F.d)) :
    atPlace F.d w (l₁ ++ l₂) = atPlace F.d w l₁ ++ atPlace F.d w l₂ := by
  simp [atPlace, List.filterMap_append]

private theorem atPlace_rep (w : Pl E) (k : ℕ) :
    atPlace F.d w (List.replicate k (Sum.inl ())) = [] := by
  induction k with
  | zero => simp [atPlace]
  | succ k ih => simpa [atPlace, List.replicate_succ] using ih

private theorem atPlace_lw (w : Pl E) (ws : List (List (F.Γ × Bool))) :
    atPlace F.d w (lw F ws) = atPlace F.d w (ws.flatten.map (lt F)) := by
  induction ws with
  | nil => simp [UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw, atPlace]
  | cons v ws ih =>
    rw [lw_cons, atPlace_append, atPlace_append, ih, atPlace_rep, List.flatten_cons, List.map_append,
      atPlace_append, List.nil_append]

private theorem sph_word (w : Pl E) (l : List (F.Γ × Bool)) :
    U.UGen.sph (l.map (ul F)) w = MLM.wordUS F.d w (atPlace F.d w (l.map (lt F))) := by
  induction l with
  | nil => simp [U.UGen.sph, MLM.wordUS, atPlace]
  | cons p l ih =>
    have hs : ∀ (x : U.UGen E n) (l' : List (U.UGen E n)), U.UGen.sph (x :: l') w =
        Sum.elim (fun _ => U.UGen.sph l' w) (fun y : Σ w : Pl E, UL n w → ℂ =>
          if h : y.1 = w then lconv (h ▸ y.2) (U.UGen.sph l' w) else U.UGen.sph l' w) x := fun _ _ => rfl
    rcases p with ⟨(u | y | x), b⟩
    · have h1 : atPlace F.d w (lt F (Sum.inl u, b) :: l.map (lt F)) = atPlace F.d w (l.map (lt F)) := by
        simp [atPlace, lt]
      rw [List.map_cons, List.map_cons, h1, ← ih, hs]
      cases b <;> simp [ul, RunFrame.ug, U.UGen.adj]
    · have h1 : atPlace F.d w (lt F (Sum.inr (Sum.inl y), b) :: l.map (lt F)) = atPlace F.d w (l.map (lt F)) := by
        simp [atPlace, lt]
      rw [List.map_cons, List.map_cons, h1, ← ih, hs]
      cases b <;> simp [ul, RunFrame.ug, U.UGen.adj]
    · rw [List.map_cons, List.map_cons, hs]
      by_cases h : x.1.1 = w
      · subst h
        have h1 : atPlace F.d x.1.1 (lt F (Sum.inr (Sum.inr x), b) :: l.map (lt F)) =
            (x.2.1, x.2.2, b) :: atPlace F.d x.1.1 (l.map (lt F)) := by
          simp [atPlace, lt]
        rw [h1]
        have h2 : MLM.wordUS F.d x.1.1 ((x.2.1, x.2.2, b) :: atPlace F.d x.1.1 (l.map (lt F))) =
            lconv (if b then lstar (F.d.hU x.1.1 x.2.1) else F.d.hU x.1.1 x.2.1)
              (MLM.wordUS F.d x.1.1 (atPlace F.d x.1.1 (l.map (lt F)))) := rfl
        rw [h2, ← ih]
        cases b <;> simp [ul, RunFrame.ug, U.UGen.adj]
      · have h1 : atPlace F.d w (lt F (Sum.inr (Sum.inr x), b) :: l.map (lt F)) =
            atPlace F.d w (l.map (lt F)) := by
          simp [atPlace, lt, h]
        rw [h1, ← ih]
        cases b <;> simp [ul, RunFrame.ug, U.UGen.adj, h]

end

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.usph_pf :
    USph := by
  intro hR E _ _ _ n π S T F₀ F ws
  refine ⟨count_lw F ws, fun w => ?_⟩
  rw [atPlace_lw, sph_word]

end
