import Formalism.LocalToGlobal.CharacterGerms.IntSProd

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem cc_smul {σ : Type} (c : C) {F : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (c • F) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hF, mul_zero]

theorem expS_copies (Y : FBChart C V O dd) (n : ℕ) :
    FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) =
      ∏ b : Fin n, ev (n := n) ![pt C dd b] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) := by
  have ha : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (![pt C dd b] s.1 s.2) = 0 := by
    intro b s
    simp [pt]
  have hc : ∀ b : Fin n, MvPowerSeries.constantCoeff (ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) = 0 := fun b =>
    (ordGE_one_iff _).1 (ordGE_subst (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))
      ((ordGE_one_iff _).2 (VP.cc_hL Y)))
  have hs : ∀ b : Fin n, ev (n := n) ![pt C dd b] ((Y.k : C) • Y.B.hL C Y.h Y.w0) =
      (Y.k : C) • ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0) := fun b =>
    MvPowerSeries.subst_smul (hasSubst_of_ordGE (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))) _ _
  rw [VP.expS_eq _ (cc_smul _ (by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hc b)), Finset.smul_sum,
    Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun b _ => cc_smul _ (hc b))]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [VP.expS_eq _ (cc_smul _ (VP.cc_hL Y))]
  show _ = MvPowerSeries.subst (fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (mvExp _)
  rw [VP.subst_exp (ha b) (cc_smul _ (VP.cc_hL Y))]
  exact congrArg mvExp (hs b).symm

theorem rowCopy_mul_exp {J : Fin 2 → Type} {n : ℕ} (b : Fin n) (F L : MvPowerSeries (WV J) C) :
    rowCopy b (F * mvExp L) = rowCopy b F * mvExp (rowCopy b L) := by
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq, rtj_rowCopy_eq, map_mul]
  congr 1
  ext x
  rw [MvPowerSeries.coeff_rename]
  show _ = ∑ k ∈ Finset.range (x.degree + 1),
    MvPowerSeries.coeff x ((MvPowerSeries.rename (rtjR b) L) ^ k) / (k.factorial : C)
  simp_rw [← map_pow, MvPowerSeries.coeff_rename, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hdeg : y.degree = x.degree := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_preimage] at hy
    rw [← hy, Finsupp.degree_mapDomain]
  show ∑ k ∈ Finset.range (y.degree + 1), _ = _
  rw [hdeg]

end VP

theorem valuation_eq_pair_of_cuts : ValEqPFromCutsSt := by
  intro C _ _ V O _ _ dd d _ Orb _ I _ Y p H Ls n h1 h2 h3 h4 hs P hP Po hQ kind hk S t ht gr hg
  obtain ⟨U, hUi, hU0, hUeq⟩ := h2 hs
  obtain ⟨U', hU'i, hU'U⟩ := VP.intInv hUi hU0
  choose G hGi hGe using fun o ρ => h3 hs o (S o) (t o) (ht o) (gr o ρ) (hg o ρ)
  have hpt : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (![pt C dd b] s.1 s.2) = 0 := by
    intro b s
    simp [pt]
  have hpti : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, IntS V (![pt C dd b] s.1 s.2) := by
    intro b s
    simp only [Matrix.cons_val_fin_one, pt]
    exact VP.IntS_X _
  have hb : ∀ b : Fin n, pull1 Y p (U' * ∏ o, G o b) * pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      ∏ o, toAllS o (gr o b * mvExp (Y.raw (p o)).hRow) := by
    intro b
    have e1 : pull1 Y p U' * pull1 Y p U = 1 := by rw [← VP.pullback_one_var_mul, hU'U, VP.pullback_one_var_one]
    rw [hUeq, VP.pullback_one_var_mul, VP.pullback_one_var_prod]
    simp only [hGe, VP.toAllS_mul]
    rw [Finset.prod_mul_distrib]
    calc pull1 Y p U' * (∏ o, toAllS o (gr o b)) * (pull1 Y p U * ∏ o, toAllS o (mvExp (Y.raw (p o)).hRow))
        = (pull1 Y p U' * pull1 Y p U) * ((∏ o, toAllS o (gr o b)) * ∏ o, toAllS o (mvExp (Y.raw (p o)).hRow)) := by
          ring
      _ = _ := by rw [e1, one_mul]
  have hpull : pullN Y p ((∏ b : Fin n, ev (n := n) ![pt C dd b] (U' * ∏ o, G o b)) *
      ∏ b : Fin n, ev (n := n) ![pt C dd b] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      ∏ o, MvPowerSeries.rename (VP.eAll n o)
        (∏ ρ : Fin n, (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.raw (p o)).hRow))) := by
    rw [VP.pullN_mul, VP.pullN_prod, VP.pullN_prod, ← Finset.prod_mul_distrib]
    simp only [VP.pullN_ev, ← VP.rowOf_mul, hb, VP.rowOf_prod, VP.rowOf_toAllS, VP.rowCopy_mul_exp, map_prod]
    exact Finset.prod_comm
  refine ⟨∏ b : Fin n, ev (n := n) ![pt C dd b] (U' * ∏ o, G o b), ?_, ?_⟩
  · exact VP.IntS_prod _ fun b _ =>
      IntS.subst (hpt b) (hpti b) (IntS.mul hU'i (VP.IntS_prod _ fun o _ => hGi o b))
  · unfold FBChart.nab nabValN
    rw [h1 n (Ls.ι n) (Ls.cp n) (Ls.uv n) P _ hQ, VP.expS_copies Y n, hpull, VP.jet_orb]
    exact Finset.prod_congr rfl fun o _ =>
      h4 C V d (I o) (Fin dd) (Y.raw (p o)) (H o) n (Po o) (kind o) (hk o) (gr o)

theorem valuation_eq_pair_of_log_unit_germ {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
    (h1 : LogCoordSt Y p) (h2 : UnitSt Y p) (h3 : GermLiftSt Y p H) : ValEqPSt Y p H Ls n := valuation_eq_pair_of_cuts C V O dd d Orb I Y p H Ls n h1 h2 h3 leaf_holds

end Formalism.L2.FormalSeriesBounds
