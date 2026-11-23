import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts

noncomputable section

namespace Formalism.MainNotions.product_zeroth_first_parts

theorem kvalGe_anti {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {B B' : ℝ} (hB : B' ≤ B) (h : KvalGe N0 N1 l nu Th B) :
    KvalGe N0 N1 l nu Th B' := by
  intro I m
  have hl : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  exact (h I m).trans (Real.rpow_le_rpow_of_exponent_le hl (neg_le_neg hB))

theorem logb_add_one_nonneg {l : ℕ} (hl : 1 < l) {a : ℝ} (ha : (l : ℝ) ≤ a) : 0 ≤ Real.logb l a + 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl
  have h2 := Real.logb_nonneg h1 (le_trans h1.le ha)
  linarith

theorem uniform_bound_mono {C C' : ℝ} (hC : C ≤ C') (h : ExportAllConjugates C) : ExportAllConjugates C' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun L hL => ⟨?_, ?_⟩, fun L hL => ?_⟩
  · intro a ha
    refine kvalGe_anti _ _ _ _ _ ?_ ((h1 L hL).1 a ha)
    have hl : 1 < L.l := (Fact.out : L.l.Prime).one_lt
    have hX : 0 ≤ (L.d : ℝ) * L.N0 * L.N1 * (Real.logb L.l a + 1) :=
      mul_nonneg (by positivity) (logb_add_one_nonneg hl ha.1)
    have hCX := mul_le_mul_of_nonneg_right hC hX
    linarith
  · intro a ha k w E hk hw hE h1' h2'
    refine kvalGe_anti _ _ _ _ _ ?_ ((h1 L hL).2 a ha k w E hk hw hE h1' h2')
    have hl : 1 < L.l := (Fact.out : L.l.Prime).one_lt
    have hX : 0 ≤ (L.d : ℝ) * L.N0 * L.N1 * (Real.logb L.l a + 1) :=
      mul_nonneg (by positivity) (logb_add_one_nonneg hl ha.1)
    have hCX := mul_le_mul_of_nonneg_right hC hX
    have h3 : C * (∑ s, w s) / (L.l : ℝ) ≤ C' * (∑ s, w s) / (L.l : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun s _ => (hw s).le)) (Nat.cast_nonneg _)
    linarith
  · intro a ha
    refine kvalGe_anti _ _ _ _ _ ?_ (h2 L hL a ha)
    have hl : 1 < L.l := (Fact.out : L.l.Prime).one_lt
    have hX : 0 ≤ (L.N0 : ℝ) * L.N1 * (Real.logb L.l a + 1) :=
      mul_nonneg (by positivity) (logb_add_one_nonneg hl ha.1)
    have hCX := mul_le_mul_of_nonneg_right hC hX
    linarith

end Formalism.MainNotions.product_zeroth_first_parts

end
