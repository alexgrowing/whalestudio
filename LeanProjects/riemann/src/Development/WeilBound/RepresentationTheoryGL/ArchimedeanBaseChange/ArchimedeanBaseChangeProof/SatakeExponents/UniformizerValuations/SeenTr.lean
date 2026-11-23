import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def LocData.IsLetter {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (d : LocData E n) (a : ℕ) (ha : a ≤ n)
    (L : LM d.kap a (n - a)) : Prop :=
  d.IsGen a ha L ∨ (∃ L', d.IsGen a ha L' ∧ L = L'.adj) ∨ L = d.betaL a ha ∨ L = d.fixL a

def SeenTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n)
  (ls : List (LM d.kap a (n - a))) (N : ∀ w, d.kap w → d.kap w → ℂ), (∀ L ∈ ls, d.IsLetter a ha L) → ∀ w ∈ d.B,
    (ls.foldr LM.mul (d.eL a)).t w = idem (d.lev₂ a w) ∧
    ((w ∈ d.T → ¬ GlobalTheory.UnitaryBC.IsSplitAt w) →
      seen ((ls.foldr LM.mul (d.eL a)).tr d.P N) (ls.foldr LM.mul (d.eL a)).t w = (ls.foldr LM.mul (d.eL a)).tr d.P N w)

theorem lmWd_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : Pl E → Type} [∀ w, Fintype (κ w)] {B : Block E}
    (Lo : PT B → LM κ B.a B.b) (w : List (BGen B)) (L₀ : LM κ B.a B.b) :
    lmWd Lo w L₀ = ((w.filterMap Sum.getRight?).map Lo).foldr LM.mul L₀ := by
  induction w with
  | nil => rfl
  | cons g w ih => cases g <;> simp [lmWd, List.filterMap_cons] at ih ⊢ <;> rw [ih]

end PositivityTheory.Rg.BcB.F

end
