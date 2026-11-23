import Formalism.LocalToGlobal.CharacterGerms.UncurryLinearCombination
import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroFirstThenZero
import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroDoubleMultiplicationPair
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAddCvSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelfCuts

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def NoLinSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (g : Fin 2) (a0 : ZMod d) (u0 : Fin dd → C), (∀ i, V.Ge 0 (u0 i)) →
    (∀ β, linAct (Y.B.A.act β) u0 = p.em a0 β • u0) → Y.FirstVanishingAt u0 →
    (∀ q : I0, V.MM (∑ col, Y.aLin (fun i => p.gm a0 col g * u0 i)
      (fun i => p.gm (p.ty0 q) col (1 - g) * p.e q i))) →
    ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) → V.MM (Y.aLin u0 v)

namespace SelfAdjointTop

open MaximalIdealCongruence

variable {C : Type} [Field C]

theorem not_mm_one {V : VF C} : ¬ V.MM (1 : C) := by
  intro h
  have h1 : (0 : WithTop ℝ) < V.v 1 := h
  rw [AddValuation.map_one] at h1
  exact lt_irrefl _ h1

theorem mm_of_unit_mul {V : VF C} {c x : C} (hc : ¬ V.MM c) (hc0 : V.Ge 0 c) (h : V.MM (c * x)) : V.MM x := by
  have hc0' : (0 : WithTop ℝ) ≤ V.v c := hc0
  have hc' : ¬ (0 : WithTop ℝ) < V.v c := hc
  have h0 : V.v c = 0 := le_antisymm (not_lt.mp hc') hc0'
  have h1 : (0 : WithTop ℝ) < V.v (c * x) := h
  rw [AddValuation.map_mul, h0, zero_add] at h1
  exact h1

theorem tyS_coeff_l {l : ℕ} (hl : 2 ≤ l) (f : ℕ → C) : PowerSeries.coeff l (tyS l f) = f 1 := by
  unfold tyS
  rw [PowerSeries.coeff_mk, Finset.sum_eq_single 1]
  · rw [pow_one, if_pos rfl]
  · intro s _ hs
    rw [if_neg]
    intro h
    apply hs
    have h' : l ^ s = l ^ 1 := by rw [pow_one]; exact h
    exact Nat.pow_right_injective hl h'
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

theorem linAct_comb {dd : ℕ} {ι : Type} [Fintype ι] (φ : Pt C 1 dd) (w : ι → C) (e : ι → Fin dd → C) :
    linAct φ (fun i => ∑ c, w c * e c i) = fun i => ∑ c, w c * linAct φ (e c) i := by
  funext i
  unfold linAct
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem coeff_aOf_smul (Y : FBChart C V O dd) (c : C) (u : Fin dd → C) (ν : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.coeff ν (Y.aOf fun i => c * u i) = c ^ V.l * MvPowerSeries.coeff ν (Y.aOf u) := by
  show ∑ i, (c * u i) ^ V.l * _ = c ^ V.l * ∑ i, u i ^ V.l * _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, mul_assoc]

theorem aLin_single (Y : FBChart C V O dd) (u : Fin dd → C) (j : Fin dd) :
    Y.aLin u (Pi.single j 1) = MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.aOf u) := by
  unfold FBChart.aLin
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, one_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem first_vanishing_of_unit_smul (Y : FBChart C V O dd) {c : C} (hc : ¬ V.MM c) (hc0 : V.Ge 0 c) {u : Fin dd → C}
    (h : Y.FirstVanishingAt fun i => c * u i) : Y.FirstVanishingAt u := by
  intro k
  have hk := h k
  have e : ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * (c * u i) ^ V.l =
      c ^ V.l * ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * u i ^ V.l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]; ring
  rw [e] at hk
  exact mm_of_unit_mul (fun h' => hc (mm_of_pow h')) (hc0.pow _) hk

end SelfAdjointTop

open SelfAdjointTop MaximalIdealCongruence in

theorem rank_maximal_self_core (hV1 : FirstVanishingCore) (hFE : FunEqCoreSt) (hC0 : CurveLinearTermCondition) (hNL : NoLinSelfSt) :
    RankMaximalSelfOfNondegenerate := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p hN hrk Hc hAlt g a hbig w x hG hc0 c
  by_contra hwc
  have hl := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, hlg, hfil⟩ := ((Y.rawSelf p).mem_tySet_iff V g x).1 hG.1.1
  have h0 : x 0 = Sum.elim w 0 := hG.1.2.1
  have h1 : ∀ c, x 1 (Sum.inl c) = 0 := hG.2
  have hγ0 : ∀ s, MvPowerSeries.constantCoeff (γ s) = 0 := fun s => (hγ s).1

  obtain ⟨a0, ha0⟩ : ∃ a0 : ZMod d, ∀ c : I0, w c ≠ 0 → p.ty0 c = a0 := by
    refine ⟨if g = 0 then a else a + p.hd, fun c' hw => ?_⟩
    by_contra hne
    apply hw
    have h2 := hG.1.2.2 0 (Sum.inl c') (by
      show (if g = 0 then p.ty0 c' else p.ty0 c' + p.hd) ≠ a + ((0 : ℕ) : ZMod d)
      rw [Nat.cast_zero, add_zero]
      by_cases hg : g = 0
      · rw [if_pos hg] at hne ⊢
        exact hne
      · rw [if_neg hg] at hne ⊢
        intro h3
        apply hne
        rw [← h3, add_assoc, p.hd_two, add_zero])
    rw [h0] at h2
    exact h2
  have hwI : ∀ c : I0, V.Ge 0 (w c) := fun c' => by
    have h2 := (Hc g).t2 x hG.1.1 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) (Sum.inl c')
    rw [h0] at h2
    exact h2
  let u0 : Fin dd → C := fun i => ∑ c : I0, w c * p.e c i
  let U : Fin 2 → Fin dd → C := fun col i => p.gm a0 col g * u0 i
  let γc : Fin 2 → Fin dd → PowerSeries C := fun col i => γ (col, i)
  have hu0I : ∀ i, V.Ge 0 (u0 i) := fun i => VF.Ge.sum fun c' _ => VF.Ge.mul_int (hwI c') (p.e_int c' i)
  have hgI : ∀ b r s, V.Ge 0 (p.gm b r s) := fun b r s => SelfData.gm_int Y p b r s
  have hUI : ∀ col i, V.Ge 0 (U col i) := fun col i => VF.Ge.mul_int (hgI _ _ _) (hu0I i)
  have hU : ∀ col i, ∑ c : I0, (Y.rawSelf p).u g c (col, i) * w c = U col i := by
    intro col i
    show ∑ c : I0, (p.gm (p.ty0 c) col g * p.e c i) * w c = p.gm a0 col g * ∑ c : I0, w c * p.e c i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    by_cases hw : w c' = 0
    · rw [hw]; ring
    · rw [ha0 c' hw]; ring
  have hcv : ∀ col, IsCv V (γc col) := fun col i => hγ (col, i)
  have hcol : ∀ (col : Fin 2) (f : MvPowerSeries (Fin dd) C), alongCv γ (inCol col f) = alongCv (γc col) f :=
    fun col f => subst_inCol hγ0 col f
  have hLg : ∀ col, Y.LgLin (γc col) (U col) := by
    intro col i
    have h2 : alongCv (γc col) (un1 (Y.lg i)) =
        ∑ c : I0, (Y.rawSelf p).u g c (col, i) • tyS V.l (fun s => x s (Sum.inl c)) := by
      rw [← hcol]
      exact hlg (col, i)
    rw [h2, ← hU]
    exact agr_of_ty (I := fun _ => I0) h0 h1 _

  obtain ⟨col, hcolU⟩ : ∃ col, ¬ V.MM (p.gm a0 col g) := by
    by_contra hall
    push Not at hall
    apply not_mm_one (V := V)
    rw [← SelfData.gm_pair Y p a0 g]
    exact mm_sum _ _ fun r _ => mm_mul_ge (hall r) (hgI _ _ _)
  have hV1U : ∀ r, Y.FirstVanishingAt (U r) := fun r => hV1 C V O dd Y (γc r) (U r) (hcv r) (hLg r)
  have hV1u : Y.FirstVanishingAt u0 := first_vanishing_of_unit_smul Y hcolU (hgI _ _ _) (hV1U col)
  have heig : ∀ β, linAct (Y.B.A.act β) u0 = p.em a0 β • u0 := by
    intro β
    show linAct (Y.B.A.act β) (fun i => ∑ c : I0, w c * p.e c i) = _
    rw [linAct_comb]
    funext i
    show ∑ c : I0, w c * linAct (Y.B.A.act β) (p.e c) i = p.em a0 β * ∑ c : I0, w c * p.e c i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [p.e_eig]
    show w c' * (p.em (p.ty0 c') β * p.e c' i) = _
    by_cases hw : w c' = 0
    · rw [hw]; ring
    · rw [ha0 c' hw]; ring

  have hlink : ∀ q : I0, V.MM (∑ r, Y.aLin (U r) (fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i)) := by
    intro q
    have hq := congrArg (PowerSeries.coeff V.l) (hfil q)
    rw [tyS_coeff_l hl, map_add, map_sub, map_sum] at hq
    have hz : ∑ c : I0, PowerSeries.coeff V.l (if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
        (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun c' _ => ?_
      split_ifs
      · rw [map_smul, tyS_coeff_l hl, h1 c', smul_zero]
      · rw [map_zero]
    rw [hz, add_zero] at hq
    have hsg : alongCv γ ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) =
        ∑ r, alongCv (γc r) (un1 (Y.sgP fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i)) := by
      rw [Y.rawSelf_sg p, Fin.sum_univ_two, Fin.sum_univ_two, ← hcol, ← hcol, Y.rawCol_sg, Y.rawCol_sg]
      exact MvPowerSeries.subst_add (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0) _ _
    rw [hsg, map_sum] at hq
    have hc := hc0 q
    have hc' : V.MM ((V.l : C) * x 1 (Sum.inr q)) := hc
    rw [hq] at hc'
    have hvI : ∀ r i, V.Ge 0 (p.gm (p.ty0 q) r (1 - g) * p.e q i) :=
      fun r i => VF.Ge.mul_int (hgI _ _ _) (p.e_int q i)
    have hL := fun r => hC0 C V O dd Y (γc r) (U r) (hcv r) (hLg r) _ (hvI r)
    have e : ∑ r, Y.aLin (U r) (fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i) =
        (V.l : C) * PowerSeries.coeff V.l (lam q) -
          (V.l : C) * (PowerSeries.coeff V.l (lam q) -
            ∑ r, PowerSeries.coeff V.l (alongCv (γc r) (un1 (Y.sgP fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i)))) -
          ∑ r, ((V.l : C) * PowerSeries.coeff V.l
            (alongCv (γc r) (un1 (Y.sgP fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i))) -
              Y.aLin (U r) (fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [e]
    exact mm_sub (mm_sub (mm_l_mul ((hlam q).2 _)) hc') (mm_sum _ _ fun r _ => hL r)
  have hnl := hNL C V O dd Y d I0 p g a0 u0 hu0I heig hV1u hlink

  have hfun : (fun i => PowerSeries.coeff 1 (γc col i)) = U col :=
    funext fun i => coeff1_of_lgLin Y (hcv col) (hLg col) i
  obtain ⟨b, hb, hbc⟩ := first_step_second_half C V Y.algClosed dd Y.B.G Y.intF (Y.aOf (U col)) (Y.chartLinearTerm (U col))
    (intS_aOf Y (first_unit_series_integral C V O dd Y) _ (hUI col)) (intS_c2lin Y _ (hUI col))
    (fun j => by
      rw [coeff_aOf_smul Y (p.gm a0 col g) u0, ← aLin_single]
      refine mm_mul_ge' ((hgI _ _ _).pow _) (hnl _ fun i => ?_)
      by_cases hij : i = j
      · subst hij; rw [Pi.single_eq_same]; exact VF.Ge.one
      · rw [Pi.single_eq_of_ne hij]; exact VF.Ge.zero 0)
    (hFE C V O dd Y (U col) (hUI col) (hV1U col))
  refine hN (γc col) (hcv col) ?_ ?_ ⟨b, hb, ?_⟩
  · by_contra hall
    push Not at hall
    apply hwc
    have hall' : ∀ i, V.MM (U col i) := fun i => by rw [← congrFun hfun i]; exact hall i
    have hu0M : ∀ i, V.MM (u0 i) := fun i => mm_of_unit_mul hcolU (hgI _ _ _) (hall' i)
    obtain ⟨wd, hwd, hsat⟩ := p.e_sat
    have e : w c = ∑ i, u0 i * wd i c := by
      show w c = ∑ i, (∑ c' : I0, w c' * p.e c' i) * wd i c
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ c' : I0, ∑ i, w c' * p.e c' i * wd i c = w c' * (if c' = c then 1 else 0) := by
        intro c'
        rw [← hsat c' c, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e]
    exact mm_sum _ _ fun i _ => mm_mul_ge (hu0M i) (hwd i c)
  · intro i μ hμ0 hμ1
    rw [hom_of_lgLin Y (hcv col) (hLg col) i μ hμ0 hμ1]
    exact mm_zero
  · rw [hfun]
    exact hbc

end Formalism.L2.FormalSeriesBounds
