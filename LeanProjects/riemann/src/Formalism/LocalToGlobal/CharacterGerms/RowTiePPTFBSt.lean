import Formalism.LocalToGlobal.CharacterGerms.RowTieCartTop

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

def PTExFBSt : Prop :=
  AllFB fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, ∀ c, x 0 (Sum.inl c) = w c

def PTAvgFBSt : Prop :=
  AllFB fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (x : ℕ → I g ⊕ JJ I g → C), x ∈ X.TySet V g →
    (∀ n, X.tyC g n ≠ a → x 0 n = 0) →
    ∃ x' ∈ X.TySet V g, x' 0 = x 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x' i n = 0

theorem ptFB_of (hEx : PTExFBSt) (hAvg : PTAvgFBSt) (hG : GermIAllSt) (hStab : HStabFBSt) : PTFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g a w hw hty
  obtain ⟨x, hx, hx0⟩ := hEx C V O dd Y d I p g a w hw hty

  have hint : ∀ n, V.Ge 0 (x 0 n) :=
    (Y.raw p).val_nonneg_leading_coeff_of_mem_tySet V g (Y.raw_lin p) (Y.raw_axis0 p) (p.u_sat g) (hStab C V O dd Y d I p g) x hx 0
      (fun i hi => absurd hi (Nat.not_lt_zero i))
  set ζ : JJ I g → C := fun q => -x 0 (Sum.inr q) with hζ
  have hζi : ∀ q, V.Ge 0 (ζ q) := fun q => VF.Ge.neg (hint _)
  have h3 := (Y.raw p).const_mem_type_set_of_nonneg (Y.chart_log_constantCoeff p) (Y.raw_axis0 p) V g ζ hζi
  have hx1 := (Y.raw p).add_mem V g (addCvFB_of hG C V O dd Y d I p) p.u_int x _ hx h3
  have e0 : (x + const0 (Sum.elim 0 ζ) : ℕ → I g ⊕ JJ I g → C) 0 = Sum.elim w 0 := by
    funext n
    cases n with
    | inl c => simp [const0, hx0 c]
    | inr q => simp [const0, hζ]
  obtain ⟨x', hx', hx'0, hpure⟩ := hAvg C V O dd Y d I p g a _ hx1 (by
    intro n hn
    rw [e0]
    cases n with
    | inl c => exact hty c hn
    | inr q => rfl)
  exact ⟨x', hx', hx'0.trans e0, hpure⟩

end Formalism.L2.FormalSeriesBounds
