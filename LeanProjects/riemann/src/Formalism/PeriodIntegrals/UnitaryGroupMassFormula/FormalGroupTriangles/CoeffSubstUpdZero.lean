import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem

noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)

variable {K : Type*} [Field K] {σ : Type*} [Finite σ] [DecidableEq σ]

def upd (k : σ) (t : MvPowerSeries σ K) : σ → MvPowerSeries σ K := Function.update MvPowerSeries.X k t

theorem upd_const {k : σ} {t : MvPowerSeries σ K} (ht : MvPowerSeries.constantCoeff t = 0) (i : σ) :
    MvPowerSeries.constantCoeff (upd k t i) = 0 := by
  unfold upd
  rcases eq_or_ne i k with rfl | h
  · rw [Function.update_self]; exact ht
  · rw [Function.update_of_ne h]; exact MvPowerSeries.constantCoeff_X i

theorem hasSubst_upd (k : σ) {t : MvPowerSeries σ K} (ht : MvPowerSeries.constantCoeff t = 0) :
    MvPowerSeries.HasSubst (upd k t) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (upd_const ht)

theorem upd_self (k : σ) (t : MvPowerSeries σ K) : upd k t k = t :=
  Function.update_self _ _ _

theorem upd_ne {k i : σ} (t : MvPowerSeries σ K) (h : i ≠ k) : upd k t i = MvPowerSeries.X i :=
  Function.update_of_ne h _ _

theorem X_mem_SerS' (S : Subring K) (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ∈ SerS S σ := by
  rw [PI.AddIntG.Wk.mem_SerS]
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem upd_mem {S : Subring K} (k : σ) {t : MvPowerSeries σ K} (ht : t ∈ SerS S σ) (i : σ) :
    upd k t i ∈ SerS S σ := by
  rcases eq_or_ne i k with rfl | h
  · rw [upd_self]; exact ht
  · rw [upd_ne t h]; exact X_mem_SerS' S i

theorem prod_upd_zero (k : σ) (d : σ →₀ ℕ) :
    (d.prod fun s e => (upd k (0 : MvPowerSeries σ K) s) ^ e) =
      if d k = 0 then MvPowerSeries.monomial d 1 else 0 := by
  by_cases h : d k = 0
  · rw [if_pos h, MvPowerSeries.monomial_one_eq]
    refine Finsupp.prod_congr fun s hs => ?_
    have hsk : s ≠ k := by
      rintro rfl
      exact (Finsupp.mem_support_iff.1 hs) h
    rw [upd_ne _ hsk]
  · rw [if_neg h, Finsupp.prod]
    refine Finset.prod_eq_zero (i := k) (Finsupp.mem_support_iff.2 h) ?_
    try dsimp only
    rw [upd_self, zero_pow h]

theorem coeff_subst_upd_zero (k : σ) (f : MvPowerSeries σ K) (m : σ →₀ ℕ) (hm : m k = 0) :
    MvPowerSeries.coeff m (MvPowerSeries.subst (upd k (0 : MvPowerSeries σ K)) f) = MvPowerSeries.coeff m f := by
  have ha := hasSubst_upd k (t := (0 : MvPowerSeries σ K)) (map_zero _)
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ m]
  · try dsimp only
    rw [prod_upd_zero, if_pos hm, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    try dsimp only
    rw [prod_upd_zero]
    split_ifs
    · rw [MvPowerSeries.coeff_monomial_ne (Ne.symm hd), smul_zero]
    · rw [map_zero, smul_zero]

theorem coeff_X_mul_shift (k : σ) (H : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e + Finsupp.single k 1) (MvPowerSeries.X k * H) = MvPowerSeries.coeff e H := by
  rw [add_comm, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul]

private theorem subst_upd_subst_upd_eq_subst_upd_subst (k : σ) {t u : MvPowerSeries σ K}
    (ht : MvPowerSeries.constantCoeff t = 0) (hu : MvPowerSeries.constantCoeff u = 0) (F : MvPowerSeries σ K) :
    MvPowerSeries.subst (upd k u) (MvPowerSeries.subst (upd k t) F) =
      MvPowerSeries.subst (upd k (MvPowerSeries.subst (upd k u) t)) F := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_upd k ht) (hasSubst_upd k hu)]
  congr 1
  funext i
  try dsimp only
  rcases eq_or_ne i k with rfl | h
  · rw [upd_self, upd_self]
  · rw [upd_ne t h, upd_ne _ h, MvPowerSeries.subst_X (hasSubst_upd k hu),
      upd_ne u h]

theorem fact_div {S : Subring K} {k : σ} {s G : MvPowerSeries σ K}
    (hs0 : MvPowerSeries.constantCoeff s = 0) (hsS : s ∈ SerS S σ)
    (hsk : ∀ t : MvPowerSeries σ K, MvPowerSeries.constantCoeff t = 0 → MvPowerSeries.subst (upd k t) s = s)
    (hG : G ∈ SerS S σ) (hz : MvPowerSeries.subst (upd k s) G = 0) :
    ∃ H ∈ SerS S σ, G = (MvPowerSeries.X k - s) * H := by
  have hz0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries σ K) = 0 := map_zero _
  have hp0 : MvPowerSeries.constantCoeff (MvPowerSeries.X k + s : MvPowerSeries σ K) = 0 := by
    rw [map_add, hs0, add_zero]; exact MvPowerSeries.constantCoeff_X k
  have hm0 : MvPowerSeries.constantCoeff (MvPowerSeries.X k - s : MvPowerSeries σ K) = 0 := by
    rw [map_sub, hs0, sub_zero]; exact MvPowerSeries.constantCoeff_X k
  have hG' : MvPowerSeries.subst (upd k (MvPowerSeries.X k + s)) G ∈ PI.AddIntG.Wk.SerS S σ :=
    PI.AddIntG.Wk.mvsubst_mem_SerS S (upd_const hp0)
      (upd_mem k (add_mem (X_mem_SerS' S k) hsS)) hG
  have e0 : MvPowerSeries.subst (upd k (0 : MvPowerSeries σ K)) (MvPowerSeries.X k + s) = s := by
    rw [MvPowerSeries.subst_add (hasSubst_upd k hz0), MvPowerSeries.subst_X (hasSubst_upd k hz0),
      upd_self, hsk 0 hz0, zero_add]
  have hdvd : (MvPowerSeries.X k : MvPowerSeries σ K) ∣ MvPowerSeries.subst (upd k (MvPowerSeries.X k + s)) G := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [← coeff_subst_upd_zero k _ m hm, subst_upd_subst_upd_eq_subst_upd_subst k hp0 hz0, e0, hz, map_zero]
  obtain ⟨H', hH'⟩ := hdvd
  have hH'S : H' ∈ PI.AddIntG.Wk.SerS S σ := by
    rw [PI.AddIntG.Wk.mem_SerS]
    intro e
    rw [← coeff_X_mul_shift k H' e, ← hH']
    exact (PI.AddIntG.Wk.mem_SerS S _).1 hG' _
  refine ⟨MvPowerSeries.subst (upd k (MvPowerSeries.X k - s)) H',
    PI.AddIntG.Wk.mvsubst_mem_SerS S (upd_const hm0)
      (upd_mem k (sub_mem (X_mem_SerS' S k) hsS)) hH'S, ?_⟩
  have e1 : MvPowerSeries.subst (upd k (MvPowerSeries.X k - s)) (MvPowerSeries.X k + s) = MvPowerSeries.X k := by
    rw [MvPowerSeries.subst_add (hasSubst_upd k hm0), MvPowerSeries.subst_X (hasSubst_upd k hm0),
      upd_self, hsk _ hm0, sub_add_cancel]
  have e2 : upd k (MvPowerSeries.X k : MvPowerSeries σ K) = MvPowerSeries.X := by
    funext i
    rcases eq_or_ne i k with rfl | h
    · exact upd_self _ _
    · exact upd_ne _ h
  calc G = MvPowerSeries.subst (MvPowerSeries.X : σ → MvPowerSeries σ K) G :=
        (congrFun (MvPowerSeries.subst_self (σ := σ) (R := K)) G).symm
    _ = MvPowerSeries.subst (upd k (MvPowerSeries.X k - s))
          (MvPowerSeries.subst (upd k (MvPowerSeries.X k + s)) G) := by
        rw [subst_upd_subst_upd_eq_subst_upd_subst k hp0 hm0, e1, e2]
    _ = (MvPowerSeries.X k - s) * MvPowerSeries.subst (upd k (MvPowerSeries.X k - s)) H' := by
        rw [hH', MvPowerSeries.subst_mul (hasSubst_upd k hm0), MvPowerSeries.subst_X (hasSubst_upd k hm0),
          upd_self]

end PI.FglTriFactor.Wk
