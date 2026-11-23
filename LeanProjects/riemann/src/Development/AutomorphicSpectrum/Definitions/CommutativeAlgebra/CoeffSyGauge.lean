import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.BetaInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem coeff_sy_gauge (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (i j : Fin d) :
    algebraMap R k (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) B.sy) = sg1 k h j i - sg1 k h i j := by
  have e₁ := congrArg (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)) hc.sy
  rw [coeff_expS_two _ (coeff_swap_sub_low h hc.ax0 hc.ax1) _ (by simp)] at e₁
  rw [map_sub, coeff_ev_swap', Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single] at e₁
  have s₁ : (swE d) ((0 : Fin 2), i) = ((1 : Fin 2), i) := rfl
  have s₂ : (swE d) ((1 : Fin 2), j) = ((0 : Fin 2), j) := rfl
  rw [s₁, s₂, add_comm (Finsupp.single ((1 : Fin 2), i) 1)] at e₁
  rw [gaugeBilinearTerm_eq_neg_double_sum, gaugeBilinearTerm_eq_neg_double_sum, ← coeff_map, e₁]
  ring

theorem coeff_ad_gauge (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a : O) (i j : Fin d) :
    algebraMap R k (coeff (Finsupp.single ((0 : Fin 2), j) 1 + Finsupp.single ((1 : Fin 2), i) 1) (B.ad a)) =
      ((dAct k B (star a)).transpose * sg1 k h - sg1 k h * dAct k B a) i j := by
  have k0 : ∀ i', constantCoeff (comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i') = 0 := fun i' => by
    have : comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i' = rename (eXv d) (B.actK k a i') := eval_first_point_rename _
    rw [this, constantCoeff_rename, const_actK]
  have k1 : ∀ i', constantCoeff (comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i') = 0 := fun i' => by
    have : comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i' = rename (eZ d) (B.actK k (star a) i') :=
      eval_second_point_rename _
    rw [this, constantCoeff_rename, const_actK]
  have kX : ∀ (j' : Fin 2) (i' : Fin d), constantCoeff (pt k d j' i' : PS k 2 d) = 0 :=
    fun j' i' => constantCoeff_X _
  have c1 : ∀ j' i',
      constantCoeff ((![comp1 (B.actK k a) (pt k d 0), pt k d 1] : Fin 2 → Pt k 2 d) j' i') = 0 := by
    intro j' i'
    fin_cases j'
    exacts [k0 i', kX 1 i']
  have c2 : ∀ j' i',
      constantCoeff ((![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] : Fin 2 → Pt k 2 d) j' i') = 0 := by
    intro j' i'
    fin_cases j'
    exacts [kX 0 i', k1 i']
  have hord : ∀ e : Fin 2 × Fin d →₀ ℕ, e.degree < 2 →
      coeff e (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
        ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := fun e he => by
    rw [map_sub, coeff_ev_low B h hc _ c1 e he, coeff_ev_low B h hc _ c2 e he, sub_zero]
  have e := congrArg (coeff (Finsupp.single ((0 : Fin 2), j) 1 + Finsupp.single ((1 : Fin 2), i) 1)) (hc.ad a)
  rw [coeff_expS_two _ hord _ (degree_xz j i), map_sub, coeff_ad_side1 B h hc a i j, coeff_ad_side2 B h hc a i j,
    coeff_map] at e
  rw [e]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, gaugeBilinearTerm_eq_neg_double_sum, neg_mul, mul_neg,
    Finset.sum_neg_distrib, mul_comm (dAct k B (star a) _ i)]
  ring

end GlobalTheory.CompanionTheory.Ar.Conj
