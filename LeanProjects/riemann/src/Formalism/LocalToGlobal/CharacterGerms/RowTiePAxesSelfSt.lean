import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

theorem van_sum {τ ι : Type} {T : Set τ} (s : Finset ι) (f : ι → MvPowerSeries τ C) (hf : ∀ i ∈ s, Van T (f i)) :
    Van T (∑ i ∈ s, f i) := by
  intro ν hν
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => hf i hi ν hν)

theorem van_X {τ : Type} {T : Set τ} {q : τ} (hq : q ∈ T) : Van T (X q : MvPowerSeries τ C) := by
  intro ν hν
  rw [MvPowerSeries.coeff_X]
  split_ifs with h
  · exfalso
    exact hν q (by rw [h]; simp) hq
  · rfl

theorem van_univ {τ : Type} {f : MvPowerSeries τ C} (hf : constantCoeff f = 0) : Van Set.univ f := by
  intro ν hν
  have h0 : ν = 0 := by
    ext w
    by_contra h
    exact hν w (Finsupp.mem_support_iff.mpr h) (Set.mem_univ _)
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hf

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constantCoeff_inCol (col : Fin 2) (f : MvPowerSeries (Fin dd) C) (hf : constantCoeff f = 0) :
    constantCoeff (inCol col f) = 0 := by
  have hb : MvPowerSeries.HasSubst
      (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  unfold inCol
  rw [MvPowerSeries.constantCoeff_subst hb, finsum_eq_single _ 0]
  · simp [hf]
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : constantCoeff (d.prod fun s e => (MvPowerSeries.X (col, s) : MvPowerSeries (Fin 2 × Fin dd) C) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hi]
    rw [h0, smul_zero]

theorem van_hCol (col g : Fin 2) (h : PS C 2 dd)
    (hh : ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0) :
    Van {w : Fin 2 × (Fin 2 × Fin dd) | w.1 = g} (hCol col h) := by
  unfold hCol
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = g} (fun _ => constantCoeff_X _) ?_ ?_
  · intro s hs
    exact van_X hs
  · intro e he
    exact hh e he

theorem gauge_axes (Y : FBChart C V O dd) (g : Fin 2) :
    ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0 := by
  fin_cases g
  · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
    rfl
  · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl

theorem axesSelf_holds : AxesSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  apply RawChart.axes_of
  · intro x
    show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
    apply constantCoeff_inCol
    rw [constantCoeff_uncurry]
    exact Y.ex_const x.2
  · intro g e he
    show coeff e (∑ col, hCol col Y.h) = 0
    exact van_sum Finset.univ _ (fun col _ => van_hCol col g Y.h (gauge_axes Y g)) e he

end Formalism.L2.FormalSeriesBounds
