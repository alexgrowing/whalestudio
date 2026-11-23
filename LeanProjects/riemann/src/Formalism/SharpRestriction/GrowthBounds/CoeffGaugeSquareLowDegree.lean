import Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjOfTwo

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

open MvPowerSeries

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def Kd (r : ℕ) (f : MvPowerSeries (Fin 2) C) : Prop := ∀ i j, j < r → coeff (ee i j) f = 0

theorem Kd.mul {a b : ℕ} {f g : MvPowerSeries (Fin 2) C} (hf : Kd a f) (hg : Kd b g) : Kd (a + b) (f * g) :=
  fun i j h => kmul hf hg i j h

theorem Kd.zero' (f : MvPowerSeries (Fin 2) C) : Kd 0 f := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem Kd.pow {m : ℕ} {f : MvPowerSeries (Fin 2) C} (hf : Kd m f) (k : ℕ) : Kd (m * k) (f ^ k) := by
  induction k with
  | zero => exact Kd.zero' _
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hf

def zdeg (e : Fin 2 × κ →₀ ℕ) : ℕ := ∑ i, e (1, i)

theorem zdeg_add (e e' : Fin 2 × κ →₀ ℕ) : zdeg (e + e') = zdeg e + zdeg e' := by
  unfold zdeg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

theorem zdeg_single1 (i : κ) (k : ℕ) : zdeg (Finsupp.single ((1 : Fin 2), i) k) = k := by
  unfold zdeg
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (Prod.mk.inj h).2.symm
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem Kd_prod {a : Fin 2 × κ → MvPowerSeries (Fin 2) C} {m : ℕ} (ha : ∀ i, Kd m (a (1, i)))
    (e : Fin 2 × κ →₀ ℕ) : Kd (m * zdeg e) (e.prod fun s k => a s ^ k) := by
  induction e using Finsupp.induction_linear with
  | zero =>
    have : zdeg (0 : Fin 2 × κ →₀ ℕ) = 0 := by simp [zdeg]
    rw [this, mul_zero]
    exact Kd.zero' _
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), zdeg_add, mul_add]
    exact hf.mul hg
  | single s k =>
    rw [Finsupp.prod_single_index (h := fun s k => a s ^ k) (pow_zero _)]
    obtain ⟨g, i⟩ := s
    by_cases hg : g = 1
    · subst hg
      rw [zdeg_single1]
      exact (ha i).pow k
    · have : zdeg (Finsupp.single (g, i) k) = 0 := by
        unfold zdeg
        apply Finset.sum_eq_zero
        intro b _
        rw [Finsupp.single_apply, if_neg]
        intro h
        exact hg (Prod.mk.inj h).1
      rw [this, mul_zero]
      exact Kd.zero' _

theorem Kd_subst {a : Fin 2 × κ → MvPowerSeries (Fin 2) C} (ha0 : ∀ s, constantCoeff (a s) = 0) {m : ℕ}
    (ha : ∀ i, Kd m (a (1, i))) {f : MvPowerSeries (Fin 2 × κ) C} {r : ℕ} (hf : ∀ e, zdeg e < r → coeff e f = 0) :
    Kd (m * r) (subst a f) := by
  intro i j hj
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : zdeg e < r
  · rw [hf e he, zero_smul]
  · rw [Kd_prod ha e i j (lt_of_lt_of_le hj (Nat.mul_le_mul_left m (not_lt.1 he))), smul_zero]

theorem ee_eq_single0 {a b k : ℕ} : ee a b = Finsupp.single 0 k ↔ a = k ∧ b = 0 := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    rw [ee_zero] at h0
    rw [ee_one] at h1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    simp [ee]

theorem ee_eq_single1 {a b k : ℕ} : ee a b = Finsupp.single 1 k ↔ a = 0 ∧ b = k := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    rw [ee_zero] at h0
    rw [ee_one] at h1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    simp [ee]

theorem coeff_embedFirstVar (a b : ℕ) (f : PowerSeries C) :
    coeff (ee a b) (inV 0 f) = if b = 0 then PowerSeries.coeff a f else 0 := by
  unfold inV
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X 0))]
  simp only [coeff_X_pow, ee_eq_single0]
  by_cases hb : b = 0
  · rw [if_pos hb, finsum_eq_single _ a]
    · simp [hb]
    · intro k hk
      rw [if_neg (fun h => hk h.1.symm), smul_zero]
  · rw [if_neg hb]
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    rw [if_neg (fun h => hb h.2), smul_zero]

theorem coeff_embedSecondVar (a b : ℕ) (f : PowerSeries C) :
    coeff (ee a b) (inV 1 f) = if a = 0 then PowerSeries.coeff b f else 0 := by
  unfold inV
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X 1))]
  simp only [coeff_X_pow, ee_eq_single1]
  by_cases ha : a = 0
  · rw [if_pos ha, finsum_eq_single _ b]
    · simp [ha]
    · intro k hk
      rw [if_neg (fun h => hk h.2.symm), smul_zero]
  · rw [if_neg ha]
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    rw [if_neg (fun h => ha h.1), smul_zero]

theorem coeff_inV_mul (n j : ℕ) (P Q : PowerSeries C) :
    coeff (ee n j) (inV 1 P * inV 0 Q) = PowerSeries.coeff j P * PowerSeries.coeff n Q := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (ee 0 j, ee n 0)]
  · rw [coeff_embedSecondVar, coeff_embedFirstVar, if_pos rfl, if_pos rfl]
  · rintro ⟨p, q⟩ hpq hne
    have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
    have e0 : p 0 + q 0 = n := by
      have := DFunLike.congr_fun e 0
      simpa [ee_zero] using this
    have e1 : p 1 + q 1 = j := by
      have := DFunLike.congr_fun e 1
      simpa [ee_one] using this
    show coeff p (inV 1 P) * coeff q (inV 0 Q) = 0
    rw [eq_ee p, eq_ee q, coeff_embedSecondVar, coeff_embedFirstVar]
    by_cases hp : p 0 = 0
    · by_cases hq : q 1 = 0
      · exfalso
        apply hne
        rw [eq_ee p, eq_ee q, hp, hq]
        have h1 : p 1 = j := by omega
        have h2 : q 0 = n := by omega
        rw [h1, h2]
      · rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  · intro h
    exfalso
    apply h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext x
    fin_cases x <;> simp [ee]

def rho (F : MvPowerSeries κ C) : MvPowerSeries (Fin 2 × κ) C :=
  subst (fun x : κ => (X ((0 : Fin 2), x) : MvPowerSeries (Fin 2 × κ) C)) F

def h2 (X : RawChart C d I κ) : MvPowerSeries (Fin 2 × κ) C :=
  X.h + ∑ i, MvPowerSeries.X ((1 : Fin 2), i) * rho (X.sg (Pi.single i 1))

theorem iota_inj : Function.Injective (fun x : κ => ((0 : Fin 2), x)) := fun _ _ h => (Prod.mk.inj h).2

theorem coeff_X_mul_rho (i : κ) (F : MvPowerSeries κ C) (e : Fin 2 × κ →₀ ℕ) (h : e (1, i) = 0) :
    coeff e (MvPowerSeries.X ((1 : Fin 2), i) * rho F) = 0 := by
  rw [X_def, coeff_monomial_mul, if_neg]
  intro hle
  have := hle (1, i)
  rw [Finsupp.single_eq_same, h] at this
  omega

theorem coeff_gaugeSquare_low_degree (X : RawChart C d I κ)
    (hax : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → coeff e X.h = 0) (e : Fin 2 × κ →₀ ℕ)
    (he : zdeg e < 2) : coeff e (h2 X) = 0 := by
  unfold h2
  rw [map_add, map_sum]
  by_cases h0 : ∀ i, e (1, i) = 0
  · rw [Finset.sum_eq_zero fun i _ => coeff_X_mul_rho i _ e (h0 i), add_zero]
    apply hax
    rintro ⟨g, i⟩ hs hg
    simp only at hg
    subst hg
    exact (Finsupp.mem_support_iff.1 hs) (h0 i)
  · push Not at h0
    obtain ⟨i0, hi0⟩ := h0
    have hsum : e (1, i0) + ∑ i ∈ Finset.univ.erase i0, e (1, i) = zdeg e :=
      Finset.add_sum_erase Finset.univ (fun i => e (1, i)) (Finset.mem_univ i0)
    have h1 : e (1, i0) = 1 := by omega
    have hrest : ∑ i ∈ Finset.univ.erase i0, e (1, i) = 0 := by omega
    have hoth : ∀ i, i ≠ i0 → e (1, i) = 0 := fun i hi =>
      (Finset.sum_eq_zero_iff.1 hrest) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
    rw [Finset.sum_eq_single i0 (fun i _ hi => coeff_X_mul_rho i _ e (hoth i hi))
      (fun h => absurd (Finset.mem_univ i0) h)]
    have hle : Finsupp.single ((1 : Fin 2), i0) 1 ≤ e := by
      intro s
      by_cases hs : s = (1, i0)
      · subst hs; rw [Finsupp.single_eq_same, h1]
      · rw [Finsupp.single_apply, if_neg (fun h => hs h.symm)]; exact Nat.zero_le _
    rw [X_def, coeff_monomial_mul, if_pos hle, one_mul]
    set e' := e - Finsupp.single ((1 : Fin 2), i0) 1 with he'
    have hee : e' + Finsupp.single ((1 : Fin 2), i0) 1 = e := tsub_add_cancel_of_le hle
    have hran : (↑e'.support : Set (Fin 2 × κ)) ⊆ Set.range (fun x : κ => ((0 : Fin 2), x)) := by
      rintro ⟨g, i⟩ hs
      have hs' : e' (g, i) ≠ 0 := Finsupp.mem_support_iff.1 hs
      rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
      · exact ⟨i, rfl⟩
      · exfalso
        apply hs'
        rw [he', Finsupp.tsub_apply]
        by_cases hi : i = i0
        · subst hi; rw [Finsupp.single_eq_same, h1]
        · rw [hoth i hi]; simp
    have hmap := Finsupp.mapDomain_comapDomain (fun x : κ => ((0 : Fin 2), x)) iota_inj e' hran
    unfold rho
    rw [← hmap, coeff_subst_rename_inj _ iota_inj]
    show coeff e X.h + -∑ j, (Pi.single i0 (1 : C) : κ → C) j * coeff _ X.h = 0
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
      (fun h => absurd (Finset.mem_univ i0) h), Pi.single_eq_same, one_mul, hmap, hee, add_neg_cancel]

end SelfConjCharts

open SelfConjCharts MvPowerSeries

theorem r1sHLin_holds : GaugeLeadingTermLinear := by
  intro C _ d I _ κ _ X hax x c hx m hm hc
  set a : Fin 2 × κ → MvPowerSeries (Fin 2) C := pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (c i)) with ha
  have hc0 : ∀ i, PowerSeries.constantCoeff (c i) = 0 := fun i => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hc i 0 (by omega)
  have cc0 : ∀ (j : Fin 2) (f : PowerSeries C), PowerSeries.constantCoeff f = 0 → constantCoeff (inV j f) = 0 := by
    intro j f hf
    rw [← coeff_zero_eq_constantCoeff_apply, ← ee_00]
    fin_cases j
    · show coeff (ee 0 0) (inV 0 f) = 0
      rw [coeff_embedFirstVar, if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    · show coeff (ee 0 0) (inV 1 f) = 0
      rw [coeff_embedSecondVar, if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  have ha0 : ∀ s, constantCoeff (a s) = 0 := by
    rintro ⟨g, i⟩
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact cc0 0 _ (hx i)
    · exact cc0 1 _ (hc0 i)
  have haK : ∀ i, Kd m (a (1, i)) := by
    intro i n j hj
    show coeff (ee n j) (inV 1 (c i)) = 0
    rw [coeff_embedSecondVar]
    split_ifs
    · exact hc i j hj
    · rfl
  have hS := hasSubst_of_constantCoeff_zero ha0
  have hdec : HH X x c = subst a (h2 X) - ∑ i, inV 1 (c i) * inV 0 (alongCv x (X.sg (Pi.single i 1))) := by
    have e1 : subst a (h2 X) = subst a X.h + ∑ i, a (1, i) * subst a (rho (X.sg (Pi.single i 1))) := by
      unfold h2
      rw [subst_add hS]
      congr 1
      rw [← substAlgHom_apply hS, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [substAlgHom_apply hS, subst_mul hS, subst_X hS]
    have e2 : ∀ F : MvPowerSeries κ C, subst a (rho F) = inV 0 (alongCv x F) := by
      intro F
      unfold SelfConjCharts.rho
      rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hS]
      simp only [subst_X hS]
      exact SelfConjGauge.subst_inV 0 hx F
    simp only [e2] at e1
    rw [e1]
    show subst a X.h = _
    have : ∀ i, a (1, i) = inV 1 (c i) := fun i => rfl
    simp only [this]
    ring
  have hK2 : Kd (m * 2) (subst a (h2 X)) := Kd_subst ha0 haK (coeff_gaugeSquare_low_degree X hax)
  constructor
  · intro n j hj
    rw [hdec, map_sub, hK2 n j (by omega), map_sum, zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_inV_mul, hc i j hj, zero_mul]
  · intro n
    rw [hdec, map_sub, hK2 n m (by omega), map_sum, zero_sub]
    congr 1
    simp only [coeff_inV_mul]
    have hv : (fun i => PowerSeries.coeff m (c i)) =
        fun k => ∑ q, PowerSeries.coeff m (c q) * (Pi.single q (1 : C) : κ → C) k := by
      funext k
      rw [Finset.sum_eq_single k (fun q _ hq => by rw [Pi.single_eq_of_ne (Ne.symm hq), mul_zero])
        (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]
    rw [hv, sg_lin, alongCv_lin hx, map_sum]
    simp only [PowerSeries.coeff_smul, smul_eq_mul]

end Formalism.L2.FormalSeriesBounds
