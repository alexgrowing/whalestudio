import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PStruct

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : Pl E → Type} [∀ w, Fintype (κ w)] {S : Set (Pl E)}
  {P : Finset (Pl E)} {B : Block E} (e : B.κ ≃ ∀ w : P, κ w)

theorem fm_congr {L L' : LM κ B.a B.b} (h : L.Eqv P L') : fm S P B e L = fm S P B e L' := by
  funext x y g
  have : L.ent P (e x) (e y) = L'.ent P (e x) (e y) := by
    funext w
    unfold LM.ent
    split_ifs with hw
    · rw [h.1 w hw]
    · exact h.2.1 w hw
  simp only [fm, this, h.2.2]

theorem word_psi (hS : IsSection S) (hP : (↑P : Set (Pl E)) ⊆ S) (u₁ : GL (Fin B.a) E) (u₂ : GL (Fin B.b) E)
    (I L₀ : LM κ B.a B.b) (t₀ : PT B) (hI : I.Ok P) (h₀ : L₀.Ok P) (hI₀ : (I.mul L₀).Eqv P L₀)
    (ht : t₀.ψ = rt u₁ u₂ (fm S P B e L₀)) (w : List (BGen B × LM κ B.a B.b))
    (hw : ∀ p ∈ w, p.2.Ok P ∧ (I.mul p.2).Eqv P p.2 ∧ (∀ s, p.1 = Sum.inr s → s.ψ = fm S P B e p.2) ∧
      ∀ c, p.1 = Sum.inl c → p.2 = I) :
    ((w.map Prod.snd).foldr LM.mul L₀).Ok P ∧
      mulF B.ν (fm S P B e I) (fm S P B e ((w.map Prod.snd).foldr LM.mul L₀)) = fm S P B e ((w.map Prod.snd).foldr LM.mul L₀) ∧
      (BGen.wd (w.map Prod.fst) t₀).ψ = rt u₁ u₂ (fm S P B e ((w.map Prod.snd).foldr LM.mul L₀)) := by
  have A := BlockFiniteConvolution.fmAlg' E κ S P B e hS hP
  induction w with
  | nil => exact ⟨h₀, ((A I L₀ hI h₀).2.2.1).trans (fm_congr e hI₀), ht⟩
  | cons p w ih =>
    obtain ⟨o, i, q⟩ := ih fun p hp => hw p (List.mem_cons_of_mem _ hp)
    obtain ⟨p1, p2, p3, p4⟩ := hw p List.mem_cons_self
    have m := A p.2 _ p1 o
    simp only [List.map_cons, List.foldr_cons]
    refine ⟨m.2.1, ?_, ?_⟩
    · rw [← m.2.2.1, ← (blkLevel E B _ _ _ (A I _ hI o).1 m.1 (A _ _ o o).1).2.2.1, (A I p.2 hI p1).2.2.1, fm_congr e p2]
    · obtain ⟨g, L⟩ := p
      cases g with
      | inl c =>
        obtain rfl : L = I := p4 c rfl
        rw [← m.2.2.1, i]
        exact q
      | inr s =>
        show mulF B.ν s.ψ (BGen.wd (w.map Prod.fst) t₀).ψ = _
        rw [q, p3 s rfl, (BlockFiniteConvolution.rtAlg' E B u₁ u₂).1, m.2.2.1]

theorem adelRep2 (hS : IsSection S) (hP : (↑P : Set (Pl E)) ⊆ S) (hκ : ∀ w ∈ P, Nonempty (κ w)) (u₁ : GL (Fin B.a) E)
    (u₂ : GL (Fin B.b) E) (Ta : Ops B.Ma) (Tb : Ops B.Mb) (N : ∀ w, κ w → κ w → ℂ)
    (I L₀ : LM κ B.a B.b) (t₀ : PT B) (hI : I.Ok P) (h₀ : L₀.Ok P) (hI₀ : (I.mul L₀).Eqv P L₀)
    (ht : t₀.ψ = rt u₁ u₂ (fm S P B e L₀)) (w : List (BGen B × LM κ B.a B.b))
    (hw : ∀ p ∈ w, p.2.Ok P ∧ (I.mul p.2).Eqv P p.2 ∧ (∀ s, p.1 = Sum.inr s → s.ψ = fm S P B e p.2) ∧
      ∀ c, p.1 = Sum.inl c → p.2 = I) :
    ((w.map Prod.snd).foldr LM.mul L₀).Ok P ∧
      (BGen.wd (w.map Prod.fst) t₀).ψ = rt u₁ u₂ (fm S P B e ((w.map Prod.snd).foldr LM.mul L₀)) ∧
      trM (BGen.wd (w.map Prod.fst) t₀).Φ (opM Ta Tb (tenN P B e N)) =
        B.vol⁻¹ • adel S u₁ u₂ ((BGen.wd (w.map Prod.fst) t₀).arch Ta Tb) (((w.map Prod.snd).foldr LM.mul L₀).tr P N)
          ((w.map Prod.snd).foldr LM.mul L₀).t := by
  obtain ⟨o, -, q⟩ := word_psi e hS hP u₁ u₂ I L₀ t₀ hI h₀ hI₀ ht w hw
  exact ⟨o, q, (BlockFiniteConvolution.adelRep' E κ S P B e hS hP hκ u₁ u₂ Ta Tb N (fun _ => I) [] _ _ (fun _ h => nomatch h) o q).2.2⟩

end PositivityTheory.Rg.BcB.F

end
