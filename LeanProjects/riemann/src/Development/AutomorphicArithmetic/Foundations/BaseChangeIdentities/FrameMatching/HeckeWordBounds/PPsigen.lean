import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fm_of_eqv {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : Pl E → Type} [∀ w, Fintype (κ w)]
    (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w) {L L' : LM κ B.a B.b}
    (h : L.Eqv P L') : fm S P B e L = fm S P B e L' := by
  have hent : ∀ x y, L.ent P x y = L'.ent P x y := by
    intro x y
    funext w
    unfold LM.ent
    split_ifs with hw
    · rw [h.1 w hw]
    · rw [h.2.1 w hw]
  funext x y g
  simp only [fm, hent, h.2.2]

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psiGen_of_algebras :
    FmAlg → RtAlg → BlockProductLevels → PsiGen := by
  intro hFm hRt hLev E _ _ _ κ _ S P B e hS hPS u₁ u₂ L₀ t₀ hL₀ hid ht₀ l hl
  have alg := fun L L' (h : L.Ok P) (h' : L'.Ok P) => hFm E κ S P B e hS hPS L L' h h'
  have hrt := (hRt E B u₁ u₂).1
  have key : ∀ l : List (BGen B × LM κ B.a B.b), (∀ x ∈ l, x.2.Ok P ∧ (L₀.mul x.2).Eqv P x.2 ∧
      ((∃ c, x.1 = Sum.inl c ∧ x.2 = L₀) ∨ ∃ s, x.1 = Sum.inr s ∧ s.ψ = fm S P B e x.2)) →
      ((l.map Prod.snd).foldr LM.mul L₀).Ok P ∧
      (BGen.wd (l.map Prod.fst) t₀).ψ = rt u₁ u₂ (fm S P B e ((l.map Prod.snd).foldr LM.mul L₀)) ∧
      mulF B.ν (fm S P B e L₀) (fm S P B e ((l.map Prod.snd).foldr LM.mul L₀)) =
        fm S P B e ((l.map Prod.snd).foldr LM.mul L₀) := by
    intro l
    induction l with
    | nil =>
      intro _
      refine ⟨hL₀, ht₀, ?_⟩
      simp only [List.map_nil, List.foldr_nil]
      rw [(alg L₀ L₀ hL₀ hL₀).2.2.1]
      exact fm_of_eqv S P B e hid
    | cons x l ih =>
      intro hx
      obtain ⟨hX, hψ, hu⟩ := ih fun y hy => hx y (List.mem_cons_of_mem _ hy)
      obtain ⟨hxO, hxE, hxc⟩ := hx x List.mem_cons_self
      simp only [List.map_cons, List.foldr_cons]
      set X := (l.map Prod.snd).foldr LM.mul L₀ with hXdef
      have hOk : (x.2.mul X).Ok P := (alg x.2 X hxO hX).2.1
      have hmul : mulF B.ν (fm S P B e x.2) (fm S P B e X) = fm S P B e (x.2.mul X) := (alg x.2 X hxO hX).2.2.1
      have hunit : mulF B.ν (fm S P B e L₀) (fm S P B e (x.2.mul X)) = fm S P B e (x.2.mul X) := by
        rw [← hmul, ← (hLev E B _ _ _ (alg L₀ x.2 hL₀ hxO).1 (alg x.2 X hxO hX).1 (alg X X hX hX).1).2.2.1,
          (alg L₀ x.2 hL₀ hxO).2.2.1, fm_of_eqv S P B e hxE]
      refine ⟨hOk, ?_, hunit⟩
      rcases hxc with ⟨c, h1, h2⟩ | ⟨s, h1, h2⟩
      · have hwd : BGen.wd (x.1 :: l.map Prod.fst) t₀ = BGen.wd (l.map Prod.fst) t₀ := by
          simp [BGen.wd, h1]
        rw [hwd, hψ, ← hmul, h2, hu]
      · have hwd : BGen.wd (x.1 :: l.map Prod.fst) t₀ = s.mul (BGen.wd (l.map Prod.fst) t₀) := by
          simp [BGen.wd, h1]
        rw [hwd]
        show mulF B.ν s.ψ (BGen.wd (l.map Prod.fst) t₀).ψ = _
        rw [hψ, h2, hrt, hmul]
  exact (key l hl).2.1

end
