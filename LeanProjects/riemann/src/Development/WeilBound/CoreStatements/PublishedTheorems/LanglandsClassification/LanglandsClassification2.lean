import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace PositivityTheory.Lit1

def LanglandsClassification₂ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    ∃ (Lseg : Segment k → IrrGL k) (L : Multiset (Segment k) → IrrGL k),
      (∀ Δ, IsLSeg Δ (Lseg Δ).rep) ∧ Function.Bijective L ∧
      (∀ (𝔪 : Multiset (Segment k)) (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 →
        ∃ hd : ∑ a, (Lseg (Δ a)).1 = (L 𝔪).1, IsCosocle (L 𝔪).rep (prodIrr (fun a => Lseg (Δ a)) hd)) ∧
      ∀ 𝔪 𝔫 : Multiset (Segment k), ∃ hd : ∑ a, (![L 𝔪, L 𝔫] a).1 = (L (𝔪 + 𝔫)).1,
        jhMult (L (𝔪 + 𝔫)).rep (prodIrr ![L 𝔪, L 𝔫] hd) = 1

end PositivityTheory.Lit1

end
