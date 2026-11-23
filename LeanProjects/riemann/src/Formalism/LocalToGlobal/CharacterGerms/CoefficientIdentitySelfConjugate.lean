import Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace IndependenceBoundPlain

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
  [Fintype κ] (X : RawChart C d I κ)

def PlainCoefficientIdentity (H : ∀ g, X.CartHyp V g) : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∃ M : JJ I g → JJ I g → C, ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ c1 : JJ I g → C, (∀ q, X.ty (1 - g) q ≠ a + 2 → c1 q = 0) ∧
        ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', c1 q' * M q' q)

theorem independence_bound_raw [IsAlgClosed C] [NeZero d] (hrk : X.RankHyp) (H : ∀ g, X.CartHyp V g) (hR2 : RawChart.RankMaximalCondition H)
    (hcoef : PlainCoefficientIdentity X H) : RawChart.IndependenceBoundCondition H := by
  intro hAlt g a hbig N w x hg hV hind
  have key : ∀ g' : Fin 2, X.big g' a → X.big g' (a + 2) := by
    obtain ⟨hd, hpar⟩ := hAlt
    have hev := ValuationNonnegativity.even_val_add_two hd a
    have e1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by
      simpa using hrk.big_compl 0 b
    intro g' hb
    fin_cases g'
    · exact (hpar (a + 2)).2 (hev.2 ((hpar a).1 hb))
    · simp only [Fin.mk_one] at hb ⊢
      rw [e1, hpar] at hb ⊢
      rwa [hev]
  have hsmall : ¬ X.big (1 - g) (a + 2) := fun h2 => (hrk.big_compl g (a + 2)).1 h2 (key g hbig)
  have hcard : Fintype.card {q : JJ I g // X.ty (1 - g) q = a + 2} = X.j' := by
    rw [Fintype.card_subtype]; exact hrk.rk_small (1 - g) (a + 2) hsmall
  obtain ⟨M, hM⟩ := hcoef hAlt g a hbig
  let σ := (Fintype.equivFinOfCardEq hcard).symm
  have hspan : ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ b : Fin X.j' → C, ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ r, b r * M (σ r).1 q) := by
    intro w x hg hV
    obtain ⟨c1, hsupp, hc1⟩ := hM w x hg hV
    refine ⟨fun r => c1 (σ r).1, fun q => ?_⟩
    have hsum : ∑ q', c1 q' * M q' q = ∑ r, c1 (σ r).1 * M (σ r).1 q := by
      rw [← Finset.sum_filter_of_ne (p := fun q' => X.ty (1 - g) q' = a + 2)
        (fun q' _ hne => by
          by_contra hq
          exact hne (by rw [hsupp q' hq, zero_mul]))]
      rw [Finset.sum_subtype (Finset.univ.filter fun q' => X.ty (1 - g) q' = a + 2)
        (p := fun q' => X.ty (1 - g) q' = a + 2) (fun q' => by simp)]
      exact (Equiv.sum_comp σ (fun s => c1 s.1 * M s.1 q)).symm
    rw [← hsum]
    exact hc1 q
  exact ValuationNonnegativity.independence_bound_of_span_raw (RawChart.cart (H g)) a _ (hR2 hAlt g a hbig) (fun r => M (σ r).1) hspan
    N w x hg hV hind

end IndependenceBoundPlain

section Closed

theorem independence_bound_all_charts_of_coefficient_identity (h : CoefficientIdentityCondition) : IndependenceBoundAllCharts := by
  intro C _ _ V O _ _ dd Y d _ I _ p hrk H hR2
  have := Y.algClosed
  exact IndependenceBoundPlain.independence_bound_raw (Y.raw p) hrk H hR2 (h C V O dd Y d I p hrk H)

def CoefficientIdentitySelfConjugate : Prop :=
  AllSelf fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, IndependenceBoundPlain.PlainCoefficientIdentity X H

theorem independence_bound_self_conj (h : CoefficientIdentitySelfConjugate) : IndependenceBoundSelfConjugate := by
  unfold IndependenceBoundSelfConjugate AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p hrk H hR2
  have := Y.algClosed
  exact IndependenceBoundPlain.independence_bound_raw (Y.rawSelf p) hrk H hR2 (h C V O dd Y d I0 p hrk H)

end Closed

end Formalism.L2.FormalSeriesBounds
