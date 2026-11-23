import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgDefs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K]

section Ring
variable {ι : Type}

theorem integralMv_iff_divBy_one (F : MvPowerSeries ι K) : IntegralMv F ↔ DivByMv (1 : K) F := by
  first
  | exact Iff.rfl
  | (unfold IntegralMv DivByMv; simp)
  | simp [IntegralMv, DivByMv]
theorem integralPS_iff_mv (f : PowerSeries K) : IntegralPS f ↔ IntegralMv (ι := Unit) f := by
  rw [integralMv_iff_divBy_one]
  unfold IntegralPS DivByMv
  constructor
  · intro h d
    have hd : d = Finsupp.single () (d ()) := by
      refine Finsupp.ext fun u => ?_
      cases u
      simp
    rw [hd, norm_one]
    exact h (d ())
  · intro h n
    have := h (Finsupp.single () n)
    rw [norm_one] at this
    exact this
theorem divBy_iff_mv (x : K) (f : PowerSeries K) : DivBy x f ↔ DivByMv (ι := Unit) x f := by
  unfold DivBy DivByMv
  constructor
  · intro h d
    have hd : d = Finsupp.single () (d ()) := by
      refine Finsupp.ext fun u => ?_
      cases u
      simp
    rw [hd]
    exact h (d ())
  · intro h n
    exact h (Finsupp.single () n)
theorem divByMv_zero (x : K) : DivByMv x (0 : MvPowerSeries ι K) := by
  intro d
  rw [map_zero, norm_zero]
  exact norm_nonneg _
theorem divByMv_add {x : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv x G) :
    DivByMv x (F + G) := by
  intro d
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF d) (hG d))
theorem divByMv_sub {x : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv x G) :
    DivByMv x (F - G) := by
  intro d
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hF d) (by rw [norm_neg]; exact hG d))
theorem divByMv_neg {x : K} {F : MvPowerSeries ι K} (hF : DivByMv x F) : DivByMv x (-F) := by
  intro d
  rw [map_neg, norm_neg]
  exact hF d
theorem divByMv_mul {x y : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv y G) :
    DivByMv (x * y) (F * G) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul, norm_mul]
  refine Finset.sum_induction _ (fun z : K => ‖z‖ ≤ ‖x‖ * ‖y‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by rw [norm_zero]; positivity) ?_
  intro p _
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) (norm_nonneg _)
theorem divByMv_mul_left {x : K} {F G : MvPowerSeries ι K} (hF : IntegralMv F) (hG : DivByMv x G) :
    DivByMv x (F * G) := by
  have h := divByMv_mul ((integralMv_iff_divBy_one F).mp hF) hG
  rwa [one_mul] at h
theorem divByMv_sum {x : K} {α : Type} (s : Finset α) (F : α → MvPowerSeries ι K)
    (hF : ∀ i ∈ s, DivByMv x (F i)) : DivByMv x (∑ i ∈ s, F i) := by
  exact Finset.sum_induction _ (DivByMv x) (fun _ _ => divByMv_add) (divByMv_zero x) hF
theorem integralMv_one : IntegralMv (1 : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp
theorem integralMv_X (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp
theorem integralMv_C {c : K} (hc : ‖c‖ ≤ 1) : IntegralMv (MvPowerSeries.C c : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_C]
  split_ifs <;> simp [hc]
theorem integralMv_mul {F G : MvPowerSeries ι K} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := by
  rw [integralMv_iff_divBy_one] at *
  have h := divByMv_mul hF hG
  rwa [one_mul] at h
theorem integralMv_pow {F : MvPowerSeries ι K} (hF : IntegralMv F) (n : ℕ) : IntegralMv (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact integralMv_one
  | succ n ih => rw [pow_succ]; exact integralMv_mul ih hF

theorem divByMv_iff_smul {x : K} (hx : x ≠ 0) (F : MvPowerSeries ι K) :
    DivByMv x F ↔ ∃ G : MvPowerSeries ι K, IntegralMv G ∧ F = x • G := by
  constructor
  · intro h
    refine ⟨x⁻¹ • F, ?_, by rw [smul_smul, mul_inv_cancel₀ hx, one_smul]⟩
    refine (integralMv_iff_divBy_one _).mpr fun d => ?_
    rw [MvPowerSeries.coeff_smul, norm_mul, norm_inv, norm_one,
      inv_mul_le_iff₀ (norm_pos_iff.mpr hx), mul_one]
    exact h d
  · rintro ⟨G, hG, rfl⟩ d
    have h1 := (integralMv_iff_divBy_one G).mp hG d
    rw [norm_one] at h1
    rw [MvPowerSeries.coeff_smul, norm_mul]
    calc ‖x‖ * ‖MvPowerSeries.coeff d G‖ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖x‖ := mul_one _

end Ring

section OneVar

theorem divBy_add {x : K} {f g : PowerSeries K} (hf : DivBy x f) (hg : DivBy x g) :
    DivBy x (f + g) :=
  (divBy_iff_mv _ _).mpr (divByMv_add ((divBy_iff_mv _ _).mp hf) ((divBy_iff_mv _ _).mp hg))
theorem divBy_neg {x : K} {f : PowerSeries K} (hf : DivBy x f) : DivBy x (-f) :=
  (divBy_iff_mv _ _).mpr (divByMv_neg ((divBy_iff_mv _ _).mp hf))
theorem divBy_mul_left {x : K} {f g : PowerSeries K} (hf : IntegralPS f) (hg : DivBy x g) :
    DivBy x (f * g) :=
  (divBy_iff_mv _ _).mpr (divByMv_mul_left ((integralPS_iff_mv _).mp hf) ((divBy_iff_mv _ _).mp hg))
theorem integralPS_iff_divBy_one (f : PowerSeries K) : IntegralPS f ↔ DivBy (1 : K) f := by
  rw [integralPS_iff_mv, integralMv_iff_divBy_one, divBy_iff_mv]
theorem integralPS_X : IntegralPS (X : PowerSeries K) := by
  exact (integralPS_iff_mv _).mpr (integralMv_X ())
theorem integralPS_C {c : K} (hc : ‖c‖ ≤ 1) : IntegralPS (C c : PowerSeries K) := by
  exact (integralPS_iff_mv _).mpr (integralMv_C hc)
theorem integralPS_mul {f g : PowerSeries K} (hf : IntegralPS f) (hg : IntegralPS g) :
    IntegralPS (f * g) := by
  rw [integralPS_iff_mv] at *
  exact integralMv_mul hf hg
theorem integralPS_pow {f : PowerSeries K} (hf : IntegralPS f) (n : ℕ) : IntegralPS (f ^ n) := by
  rw [integralPS_iff_mv] at *
  exact integralMv_pow hf n
private theorem norm_natCast_le_one_unramified_integrals (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

theorem divBy_derivative {x : K} {f : PowerSeries K} (hf : DivBy x f) :
    DivBy x (derivative K f) := by
  unfold DivBy at hf ⊢
  intro n
  rw [PowerSeries.coeff_derivative, norm_mul]
  have h1 : ‖((n : K) + 1)‖ ≤ 1 := by
    have := norm_natCast_le_one_unramified_integrals (K := K) (n + 1)
    push_cast at this
    exact this
  calc ‖coeff (n + 1) f‖ * ‖((n : K) + 1)‖ ≤ ‖x‖ * 1 :=
        mul_le_mul (hf _) h1 (norm_nonneg _) (norm_nonneg _)
    _ = ‖x‖ := mul_one _
theorem integralPS_derivative {f : PowerSeries K} (hf : IntegralPS f) :
    IntegralPS (derivative K f) := by
  rw [integralPS_iff_divBy_one] at *
  exact divBy_derivative hf

theorem integralPS_inv {f : PowerSeries K} (hf : IntegralPS f) (h0 : ‖constantCoeff f‖ = 1) :
    IntegralPS f⁻¹ := by
  unfold IntegralPS at hf ⊢
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  rw [PowerSeries.coeff_inv]
  split_ifs with hn
  · rw [norm_inv, h0, inv_one]
  · rw [norm_mul, norm_neg, norm_inv, h0, inv_one, one_mul]
    refine Finset.sum_induction _ (fun z : K => ‖z‖ ≤ 1)
      (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
      (by rw [norm_zero]; exact zero_le_one) ?_
    intro p _
    split_ifs with hlt
    · rw [norm_mul]
      exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hlt)
    · rw [norm_zero]
      exact zero_le_one

theorem divBy_of_mul_unit {x : K} {f g : PowerSeries K} (hf : IntegralPS f)
    (h0 : ‖constantCoeff f‖ = 1) (h : DivBy x (f * g)) : DivBy x g := by
  have hf0 : constantCoeff f ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at h0
    exact zero_ne_one h0
  have e : g = f⁻¹ * (f * g) := by rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hf0, one_mul]
  rw [e]
  exact divBy_mul_left (integralPS_inv hf h0) h
private theorem coeff_subst_X_pow_eq_ite_dvd' (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
  have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
  rw [PowerSeries.coeff_subst' ha]
  simp only [← pow_mul, PowerSeries.coeff_X_pow]
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    rw [finsum_eq_single _ q]
    · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
    · intro d hd
      have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
      simp [this]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    have : m ≠ k * d := fun h => hd ⟨d, h⟩
    simp [this]

theorem divBy_expand_iff (x : K) (n : ℕ) (hn : n ≠ 0) (f : PowerSeries K) :
    DivBy x (f.subst ((X : PowerSeries K) ^ n)) ↔ DivBy x f := by
  unfold DivBy
  constructor
  · intro h m
    have := h (n * m)
    rwa [coeff_subst_X_pow_eq_ite_dvd' f hn, if_pos (dvd_mul_right n m),
      Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hn)] at this
  · intro h m
    rw [coeff_subst_X_pow_eq_ite_dvd' f hn]
    split_ifs
    · exact h _
    · rw [norm_zero]
      exact norm_nonneg _
theorem divByMv_expand_iff {ι : Type} (x : K) (n : ℕ) (hn : n ≠ 0) (F : MvPowerSeries ι K) :
    DivByMv x (MvPowerSeries.expand n hn F) ↔ DivByMv x F := by
  classical
  constructor
  · intro h d
    have := h (n • d)
    rwa [MvPowerSeries.coeff_expand_smul] at this
  · intro h d
    by_cases hd : ∀ i, n ∣ d i
    · have e : d = n • Finsupp.mapRange (fun k => k / n) (Nat.zero_div n) d := by
        ext i
        simp [Nat.mul_div_cancel' (hd i)]
      rw [e, MvPowerSeries.coeff_expand_smul]
      exact h _
    · push_neg at hd
      obtain ⟨i, hi⟩ := hd
      rw [MvPowerSeries.coeff_expand_of_not_dvd n hn F hi, norm_zero]
      exact norm_nonneg _

end OneVar

section Subst
variable {ι : Type}

private theorem norm_finsum_le_of_forall_norm_le {α : Type} (g : α → K) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖g i‖ ≤ C) : ‖∑ᶠ i, g i‖ ≤ C := by
  by_cases hs : (Function.support g).Finite
  · rw [finsum_eq_sum g hs]
    exact Finset.sum_induction _ (fun z : K => ‖z‖ ≤ C)
      (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
      (by rw [norm_zero]; exact hC) (fun i _ => h i)
  · rw [finsum_of_infinite_support hs, norm_zero]
    exact hC

theorem integralMv_subst {f : PowerSeries K} {P : MvPowerSeries ι K} (hf : IntegralPS f)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) : IntegralMv (f.subst P) := by
  have ha : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [norm_one]
  have hf' : ∀ k, ‖coeff k f‖ ≤ 1 := hf
  have hPk : ∀ k, ‖MvPowerSeries.coeff d (P ^ k)‖ ≤ 1 := fun k => by
    have h1 := (integralMv_iff_divBy_one _).mp (integralMv_pow hP k) d
    rwa [norm_one] at h1
  first
  | rw [PowerSeries.coeff_subst ha]
  | rw [PowerSeries.coeff_subst' ha]
  exact norm_finsum_le_of_forall_norm_le _ zero_le_one fun k => by
    rw [smul_eq_mul, norm_mul]
    exact mul_le_one₀ (hf' k) (norm_nonneg _) (hPk k)
theorem divByMv_subst {x : K} {f : PowerSeries K} {P : MvPowerSeries ι K} (hf : DivBy x f)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) : DivByMv x (f.subst P) := by
  have ha : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  intro d
  have hf' : ∀ k, ‖coeff k f‖ ≤ ‖x‖ := hf
  have hPk : ∀ k, ‖MvPowerSeries.coeff d (P ^ k)‖ ≤ 1 := fun k => by
    have h1 := (integralMv_iff_divBy_one _).mp (integralMv_pow hP k) d
    rwa [norm_one] at h1
  first
  | rw [PowerSeries.coeff_subst ha]
  | rw [PowerSeries.coeff_subst' ha]
  exact norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun k => by
    rw [smul_eq_mul, norm_mul]
    calc ‖coeff k f‖ * ‖MvPowerSeries.coeff d (P ^ k)‖ ≤ ‖x‖ * 1 :=
          mul_le_mul (hf' k) (hPk k) (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _

theorem divByMv_subst_congr {x : K} (hx : ‖x‖ ≤ 1) {f : PowerSeries K} {P Q : MvPowerSeries ι K}
    (hf : IntegralPS f) (hP0 : MvPowerSeries.constantCoeff P = 0)
    (hQ0 : MvPowerSeries.constantCoeff Q = 0) (hP : IntegralMv P) (hQ : IntegralMv Q)
    (hPQ : DivByMv x (P - Q)) : DivByMv x (f.subst P - f.subst Q) := by
  by_cases hx : x = 0
  · subst hx
    have hPQ' : P = Q := by
      ext d
      have h1 := hPQ d
      rw [norm_zero, map_sub] at h1
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
    rw [hPQ', sub_self]
    exact divByMv_zero _
  obtain ⟨R, hR, hPR⟩ := (divByMv_iff_smul hx _).mp hPQ
  have haP : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  have haQ : PowerSeries.HasSubst Q := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  have hf' : ∀ k, ‖coeff k f‖ ≤ 1 := hf
  intro d
  have hfinP := PowerSeries.coeff_subst_finite haP f d
  have hfinQ := PowerSeries.coeff_subst_finite haQ f d
  rw [map_sub, PowerSeries.coeff_subst haP, PowerSeries.coeff_subst haQ,
    ← finsum_sub_distrib hfinP hfinQ]
  refine norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun k => ?_
  have hG : IntegralMv (∑ i ∈ Finset.range k, P ^ i * Q ^ (k - 1 - i)) := by
    rw [integralMv_iff_divBy_one]
    exact divByMv_sum _ _ fun i _ =>
      (integralMv_iff_divBy_one _).mp (integralMv_mul (integralMv_pow hP i) (integralMv_pow hQ _))
  have hGR := (integralMv_iff_divBy_one _).mp (integralMv_mul hG hR) d
  rw [norm_one] at hGR
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← geom_sum₂_mul, hPR, mul_smul_comm,
    MvPowerSeries.coeff_smul, norm_mul, norm_mul]
  calc ‖coeff k f‖ * (‖x‖ * ‖MvPowerSeries.coeff d ((∑ i ∈ Finset.range k, P ^ i * Q ^ (k - 1 - i)) * R)‖)
      ≤ 1 * (‖x‖ * 1) := mul_le_mul (hf' k) (mul_le_mul_of_nonneg_left hGR (norm_nonneg _))
        (by positivity) zero_le_one
    _ = ‖x‖ := by ring
theorem divByMv_subst2 {x : K} {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : DivByMv x F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) : DivByMv x (F.subst P) := by
  have ha : MvPowerSeries.HasSubst P := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hP0
    | exact ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hprod : ∀ e : Fin 2 →₀ ℕ, IntegralMv (e.prod fun s k => P s ^ k) := by
    intro e
    unfold Finsupp.prod
    exact Finset.prod_induction _ IntegralMv (fun _ _ => integralMv_mul) integralMv_one
      (fun s _ => integralMv_pow (hP s) _)
  intro d
  rw [MvPowerSeries.coeff_subst ha]
  exact norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun e => by
    rw [smul_eq_mul, norm_mul]
    have h1 := (integralMv_iff_divBy_one _).mp (hprod e) d
    rw [norm_one] at h1
    calc ‖MvPowerSeries.coeff e F‖ * ‖MvPowerSeries.coeff d (e.prod fun s k => P s ^ k)‖
        ≤ ‖x‖ * 1 := mul_le_mul (hF e) h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _
theorem integralMv_subst2 {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : IntegralMv F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) : IntegralMv (F.subst P) := by
  rw [integralMv_iff_divBy_one] at hF ⊢
  exact divByMv_subst2 hF hP0 hP
theorem divByMv_subst2_congr {x : K} (hx : ‖x‖ ≤ 1) {F : MvPowerSeries (Fin 2) K}
    {P Q : Fin 2 → MvPowerSeries ι K} (hF : IntegralMv F)
    (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hQ0 : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) (hP : ∀ i, IntegralMv (P i))
    (hQ : ∀ i, IntegralMv (Q i)) (hPQ : ∀ i, DivByMv x (P i - Q i)) :
    DivByMv x (F.subst P - F.subst Q) := by
  have haP : MvPowerSeries.HasSubst P := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hP0
    | exact ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have haQ : MvPowerSeries.HasSubst Q := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hQ0
    | exact ⟨fun s => by rw [hQ0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hpow : ∀ i k, DivByMv x (P i ^ k - Q i ^ k) := by
    intro i k
    rw [← geom_sum₂_mul]
    refine divByMv_mul_left ?_ (hPQ i)
    rw [integralMv_iff_divBy_one]
    exact divByMv_sum _ _ fun j _ =>
      (integralMv_iff_divBy_one _).mp (integralMv_mul (integralMv_pow (hP i) j) (integralMv_pow (hQ i) _))
  have hprod : ∀ e : Fin 2 →₀ ℕ,
      DivByMv x ((e.prod fun s k => P s ^ k) - e.prod fun s k => Q s ^ k) := by
    intro e
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_two, Fin.prod_univ_two]
    have e2 : P 0 ^ e 0 * P 1 ^ e 1 - Q 0 ^ e 0 * Q 1 ^ e 1
        = P 0 ^ e 0 * (P 1 ^ e 1 - Q 1 ^ e 1) + Q 1 ^ e 1 * (P 0 ^ e 0 - Q 0 ^ e 0) := by ring
    rw [e2]
    exact divByMv_add (divByMv_mul_left (integralMv_pow (hP 0) _) (hpow 1 _))
      (divByMv_mul_left (integralMv_pow (hQ 1) _) (hpow 0 _))
  intro d
  rw [map_sub, MvPowerSeries.coeff_subst haP, MvPowerSeries.coeff_subst haQ,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite haP F d)
      (MvPowerSeries.coeff_subst_finite haQ F d)]
  refine norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun e => ?_
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, norm_mul]
  have h1 := (integralMv_iff_divBy_one F).mp hF e
  rw [norm_one] at h1
  calc ‖MvPowerSeries.coeff e F‖ *
        ‖MvPowerSeries.coeff d ((e.prod fun s k => P s ^ k) - e.prod fun s k => Q s ^ k)‖
      ≤ 1 * ‖x‖ := mul_le_mul h1 (hprod e d) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _

end Subst

section Frob
variable {l : ℕ} {σ : K →+* K} {ι : Type}

theorem FrobField.integralMv_map (h : FrobField K l σ) {F : MvPowerSeries ι K} (hF : IntegralMv F) :
    IntegralMv (MvPowerSeries.map σ F) := by
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_map, h.isom]
  exact (integralMv_iff_divBy_one F).mp hF d

theorem norm_natCast_of_coprime (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (m : ℕ) (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hint : ∀ a : ℤ, ‖(a : K)‖ ≤ 1 := by
    intro a
    rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
    · push_cast
      exact norm_natCast_le_one_unramified_integrals n
    · push_cast
      rw [norm_neg]
      exact norm_natCast_le_one_unramified_integrals n
  have hcop : Nat.gcd m l = 1 := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm).symm
  have hb := Nat.gcd_eq_gcd_ab m l
  rw [hcop] at hb
  have hbK : (1 : K) = (m : K) * (Nat.gcdA m l : K) + (l : K) * (Nat.gcdB m l : K) := by
    have := congrArg (fun z : ℤ => (z : K)) hb
    push_cast at this
    exact this
  refine le_antisymm (norm_natCast_le_one_unramified_integrals m) ?_
  by_contra hlt
  push_neg at hlt
  have h1 := IsUltrametricDist.norm_add_le_max ((m : K) * (Nat.gcdA m l : K))
    ((l : K) * (Nat.gcdB m l : K))
  rw [← hbK, norm_one] at h1
  have h2 : ‖(m : K) * (Nat.gcdA m l : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(m : K)‖ * ‖((Nat.gcdA m l : ℤ) : K)‖ ≤ ‖(m : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hint _) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hlt
  have h3 : ‖(l : K) * (Nat.gcdB m l : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖((Nat.gcdB m l : ℤ) : K)‖ ≤ ‖(l : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hint _) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hl1
  exact lt_irrefl _ (lt_of_le_of_lt h1 (max_lt h2 h3))
theorem FrobField.funEqSetting [CharZero K] (h : FrobField K l σ) : FunctionalEquationSetting K l l σ := by
  refine ⟨h.prime, ⟨1, one_pos, (pow_one l).symm⟩, h.norm_l, ?_⟩
  exact h.frob

end Frob

end ReciprocityTheory.ChartRestriction.L1
