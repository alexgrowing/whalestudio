import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero

namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

theorem multiset_prod_sub_dvd {S ι : Type*} [CommRing S] (t : S) (k : ℕ) (x y : ι → S)
    (hx : ∀ i, t ∣ x i) (hy : ∀ i, t ∣ y i) (hxy : ∀ i, t ^ k ∣ x i - y i) :
    ∀ s : Multiset ι, s ≠ 0 →
      t ^ (k + Multiset.card s - 1) ∣ (s.map x).prod - (s.map y).prod := by

  have hQ : ∀ u : Multiset ι, t ^ Multiset.card u ∣ (u.map y).prod := by
    intro u
    refine Multiset.induction_on u ?_ ?_
    · simp
    · intro b u ihu
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ']
      exact mul_dvd_mul (hy b) ihu
  intro s
  refine Multiset.induction_on s ?_ ?_
  · intro h
    exact absurd rfl h
  · intro a s ih _
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons]
    by_cases hs : s = 0
    · subst hs
      simpa using hxy a
    · have hc : Multiset.card s ≠ 0 := fun h => hs (Multiset.card_eq_zero.mp h)
      have h1 := ih hs
      have key : x a * (s.map x).prod - y a * (s.map y).prod
          = x a * ((s.map x).prod - (s.map y).prod) + (x a - y a) * (s.map y).prod := by ring
      have e : k + (Multiset.card s + 1) - 1 = (k + Multiset.card s - 1) + 1 := by omega
      rw [key, e]
      refine dvd_add ?_ ?_
      · rw [pow_succ']
        exact mul_dvd_mul (hx a) h1
      · have e2 : k + Multiset.card s - 1 + 1 = k + Multiset.card s := by omega
        rw [e2, pow_add]
        exact mul_dvd_mul (hxy a) (hQ s)

theorem finsupp_prod_eq_multiset {S ι : Type*} [CommMonoid S] (x : ι → S) (e : ι →₀ ℕ) :
    e.prod (fun i m => x i ^ m) = (e.toMultiset.map x).prod := by
  first
  | (rw [← Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)])
  | (induction e using Finsupp.induction with
      | zero => simp
      | single_add i m f hi hm ih =>
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih]
        simp [Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul])

theorem card_toMultiset_eq_degree {ι : Type*} (e : ι →₀ ℕ) :
    Multiset.card e.toMultiset = e.degree := by
  first
  | (rw [Finsupp.card_toMultiset]; rfl)
  | simp [Finsupp.card_toMultiset, Finsupp.degree, Finsupp.sum]

variable {C : Type} [Field C]

theorem subst_sub_dvd {d : ℕ} (f : MvPowerSeries (Fin d) C)
    (hf : ∀ e : Fin d →₀ ℕ, e.degree ≤ 1 → coeff e f = 0)
    (α β : Fin d → PowerSeries C) (hα : ∀ b, PowerSeries.constantCoeff (α b) = 0)
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) (k : ℕ)
    (hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ k ∣ α b - β b) :
    (PowerSeries.X : PowerSeries C) ^ (k + 1) ∣ subst α f - subst β f := by
  have hA : HasSubst α := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => hα b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => hα b)
  have hB : HasSubst β := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => hβ b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => hβ b)
  have hterm : ∀ e : Fin d →₀ ℕ, ∀ j < k + 1,
      coeff e f • PowerSeries.coeff j (e.prod (fun s n => α s ^ n)) -
        coeff e f • PowerSeries.coeff j (e.prod (fun s n => β s ^ n)) = 0 := by
    intro e j hj
    by_cases he : e.degree ≤ 1
    · rw [hf e he, zero_smul, zero_smul, sub_zero]
    · rw [← smul_sub, ← map_sub]
      have hne : e.toMultiset ≠ 0 := by
        intro h0
        have h0' : Multiset.card e.toMultiset = 0 := by rw [h0]; rfl
        rw [card_toMultiset_eq_degree] at h0'
        omega
      have hdvd := multiset_prod_sub_dvd (PowerSeries.X : PowerSeries C) k α β
        (fun b => PowerSeries.X_dvd_iff.mpr (hα b)) (fun b => PowerSeries.X_dvd_iff.mpr (hβ b)) hk
        e.toMultiset hne
      rw [card_toMultiset_eq_degree, ← finsupp_prod_eq_multiset,
        ← finsupp_prod_eq_multiset] at hdvd
      have h2 := (pow_dvd_pow (PowerSeries.X : PowerSeries C)
        (show k + 1 ≤ k + e.degree - 1 by omega)).trans hdvd
      rw [PowerSeries.X_pow_dvd_iff.mp h2 j hj, smul_zero]
  rw [PowerSeries.X_pow_dvd_iff]
  intro j hj
  rw [map_sub]
  change MvPowerSeries.coeff (Finsupp.single () j) (subst α f) -
    MvPowerSeries.coeff (Finsupp.single () j) (subst β f) = 0
  rw [MvPowerSeries.coeff_subst hA, MvPowerSeries.coeff_subst hB,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hA f _)
      (MvPowerSeries.coeff_subst_finite hB f _)]
  exact finsum_eq_zero_of_forall_eq_zero fun e => hterm e j hj

variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem coeff_lg_sub_X_low (G : LogFGL v d) (a : Fin d) (e : Fin d →₀ ℕ) (he : e.degree ≤ 1) :
    coeff e (G.lg a - X a) = 0 := by
  rw [map_sub, coeff_X]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with h0 | h1
  · have e0 : e = 0 := by
      first
      | exact (Finsupp.degree_eq_zero_iff e).mp h0
      | exact Finsupp.degree_eq_zero_iff.mp h0
    subst e0
    have hs : (0 : Fin d →₀ ℕ) ≠ Finsupp.single a 1 := by
      intro h
      have := congrArg (fun f : Fin d →₀ ℕ => f a) h
      simp at this
    rw [if_neg hs, coeff_zero_eq_constantCoeff_apply, G.lg_const a, sub_zero]
  · obtain ⟨b, hb⟩ : ∃ b, e.toMultiset = {b} := by
      apply Multiset.card_eq_one.mp
      rw [card_toMultiset_eq_degree, h1]
    have eb : e = Finsupp.single b 1 := by
      have h2 : Multiset.toFinsupp (Finsupp.toMultiset e) = e := Finsupp.toMultiset_toFinsupp e
      rw [← h2, hb]
      first
      | exact Multiset.toFinsupp_singleton b
      | simp
    subst eb
    rw [G.lg_lin a b]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : Finsupp.single b 1 ≠ Finsupp.single a 1 := by
        intro h
        exact hab ((Finsupp.single_left_inj one_ne_zero).mp h).symm
      rw [if_neg hab, if_neg hne, sub_zero]

theorem lgCurve_sub_dvd (G : LogFGL v d) {α β : Fin d → PowerSeries C}
    (hα : ∀ b, PowerSeries.constantCoeff (α b) = 0)
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) (k : ℕ)
    (hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ k ∣ α b - β b) (a : Fin d) :
    (PowerSeries.X : PowerSeries C) ^ (k + 1) ∣
      (G.lgCurve α a - G.lgCurve β a) - (α a - β a) := by
  have hA : HasSubst α := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => hα b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => hα b)
  have hB : HasSubst β := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => hβ b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => hβ b)
  have e1 : (G.lgCurve α a - G.lgCurve β a) - (α a - β a) =
      subst α (G.lg a - X a) - subst β (G.lg a - X a) := by
    show subst α (G.lg a) - subst β (G.lg a) - (α a - β a) = _
    rw [MvPowerSeries.subst_sub hA, MvPowerSeries.subst_sub hB, MvPowerSeries.subst_X hA,
      MvPowerSeries.subst_X hB]
    ring
  rw [e1]
  exact subst_sub_dvd _ (coeff_lg_sub_X_low G a) α β hα hβ k hk

theorem dvd_of_lgCurve_low (G : LogFGL v d) {α β : Fin d → PowerSeries C}
    (hα : ∀ b, PowerSeries.constantCoeff (α b) = 0)
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) :
    ∀ N : ℕ, (∀ a, ∀ j < N, PowerSeries.coeff j (G.lgCurve α a) =
      PowerSeries.coeff j (G.lgCurve β a)) →
      ∀ a, (PowerSeries.X : PowerSeries C) ^ N ∣ α a - β a
  | 0, _, a => by simp
  | N + 1, h, a => by
      have ih := dvd_of_lgCurve_low G hα hβ N (fun a j hj => h a j (by omega))
      have h1 := PowerSeries.X_pow_dvd_iff.1 (lgCurve_sub_dvd G hα hβ N ih a) N (by omega)
      rw [map_sub, map_sub, h a N (by omega), sub_self, zero_sub, neg_eq_zero] at h1
      rw [PowerSeries.X_pow_dvd_iff]
      intro j hj
      rcases Nat.lt_succ_iff.1 hj |>.lt_or_eq with hj | rfl
      · exact PowerSeries.X_pow_dvd_iff.1 (ih a) j hj
      · rw [map_sub]; exact h1

theorem coeff_lgCurve_sub_eq (G : LogFGL v d) {α β : Fin d → PowerSeries C}
    (hα : ∀ b, PowerSeries.constantCoeff (α b) = 0)
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) (N : ℕ)
    (h : ∀ a, ∀ j < N, PowerSeries.coeff j (G.lgCurve α a) = PowerSeries.coeff j (G.lgCurve β a))
    (a : Fin d) :
    PowerSeries.coeff N (G.lgCurve α a - G.lgCurve β a) = PowerSeries.coeff N (α a - β a) := by
  have hN := dvd_of_lgCurve_low G hα hβ N h
  have h1 := lgCurve_sub_dvd G hα hβ N hN a
  have h2 := PowerSeries.X_pow_dvd_iff.mp h1 N (Nat.lt_succ_self N)
  rw [map_sub] at h2
  exact sub_eq_zero.mp h2

def expC (q : ℕ) (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => PowerSeries.subst (PowerSeries.X ^ q : PowerSeries C) (ga a)

theorem expC_apply {q : ℕ} (hq : q ≠ 0) (ga : Fin d → PowerSeries C) (a : Fin d) :
    expC q ga a = PowerSeries.expand q hq (ga a) := by
  first
  | rfl
  | (simp only [expC]; rw [PowerSeries.expand_eq_subst])
  | (unfold expC; ext m; rw [PowerSeries.coeff_expand, PowerSeries.coeff_subst_X_pow] <;> simp [hq])

theorem isCurve_expC {q : ℕ} (hq : q ≠ 0) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    IsCurve v (expC q ga) := by
  intro a
  rw [expC_apply hq]
  constructor
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_expand]
    simp [(h a).1]
  · intro m
    show 0 ≤ v (PowerSeries.coeff m (PowerSeries.expand q hq (ga a)))
    rw [PowerSeries.coeff_expand]
    split_ifs
    · exact (h a).2 _
    · simp

theorem lgCurve_expC (G : LogFGL v d) {q : ℕ} (hq : q ≠ 0) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) (a : Fin d) :
    G.lgCurve (expC q ga) a = PowerSeries.expand q hq (G.lgCurve ga a) := by
  have hga : HasSubst ga := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun b => h0 b)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun b => h0 b)
  have hX : HasSubst (fun _ : Unit => (PowerSeries.X ^ q : PowerSeries C)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by first | simp [hq, PowerSeries.X] | (simp [hq]; exact PowerSeries.constantCoeff_X))
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun _ => by first | simp [hq, PowerSeries.X] | (simp [hq]; exact PowerSeries.constantCoeff_X))
  have e1 : ∀ g : PowerSeries C,
      PowerSeries.expand q hq g = PowerSeries.subst (PowerSeries.X ^ q : PowerSeries C) g :=
    fun g => (expC_apply hq (fun _ => g) a).symm
  rw [e1]
  first
  | (show MvPowerSeries.subst (expC q ga) (G.lg a) =
        MvPowerSeries.subst (fun _ => (PowerSeries.X ^ q : PowerSeries C))
          (MvPowerSeries.subst ga (G.lg a))
     rw [MvPowerSeries.subst_comp_subst_apply hga hX]
     rfl)
  | (unfold LogFGL.lgCurve PowerSeries.subst
     rw [MvPowerSeries.subst_comp_subst_apply hga hX]
     rfl)

theorem coeff_expand_rescale (q : ℕ) (hq : q ≠ 0) (x : C) (f : PowerSeries C) (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.expand q hq (PowerSeries.rescale x f)) =
      if q ∣ m then x ^ (m / q) * PowerSeries.coeff (m / q) f else 0 := by
  rw [PowerSeries.coeff_expand]
  split_ifs
  · rw [PowerSeries.coeff_rescale]
  · rfl

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
