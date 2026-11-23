import Formalism.EllipticTorsion.WChordSeries

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace WeierstrassSeriesLimit

section Series

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

def T (v : PowerSeries R) : PowerSeries R :=
  X ^ 3 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * X * v ^ 2
      + C W.a₆ * v ^ 3

def E (a b : PowerSeries R) : PowerSeries R :=
  C W.a₁ * X + C W.a₂ * X ^ 2 + C W.a₃ * (a + b) + C W.a₄ * X * (a + b)
    + C W.a₆ * (a ^ 2 + a * b + b ^ 2)

theorem T_sub (a b : PowerSeries R) : T W a - T W b = (a - b) * E W a b := by
  simp only [T, E]
  ring

theorem X_dvd_E {a b : PowerSeries R} (ha : X ∣ a) (hb : X ∣ b) : X ∣ E W a b := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  refine ⟨C W.a₁ + C W.a₂ * X + C W.a₃ * (a' + b') + C W.a₄ * X * (a' + b')
    + C W.a₆ * X * (a' ^ 2 + a' * b' + b' ^ 2), ?_⟩
  simp only [E]
  ring

theorem X_dvd_wMap {a : PowerSeries R} (ha : X ∣ a) : X ∣ T W a := by
  obtain ⟨a', rfl⟩ := ha
  refine ⟨X ^ 2 + C W.a₁ * X * a' + C W.a₂ * X ^ 2 * a' + C W.a₃ * X * a' ^ 2
    + C W.a₄ * X ^ 2 * a' ^ 2 + C W.a₆ * X ^ 2 * a' ^ 3, ?_⟩
  simp only [T]
  ring

theorem contract {k : ℕ} {a b : PowerSeries R} (ha : X ∣ a) (hb : X ∣ b) (h : X ^ k ∣ a - b) :
    X ^ (k + 1) ∣ T W a - T W b := by
  rw [T_sub, pow_succ]
  exact mul_dvd_mul h (X_dvd_E W ha hb)

omit W in
theorem eq_zero_of_forall_X_pow_dvd {d : PowerSeries R} (h : ∀ k, X ^ k ∣ d) : d = 0 := by
  ext n
  simpa using (X_pow_dvd_iff.mp (h (n + 1))) n (Nat.lt_succ_self n)

def seq : ℕ → PowerSeries R
  | 0 => 0
  | k + 1 => T W (seq k)

theorem X_dvd_seq (k : ℕ) : X ∣ seq W k := by
  induction k with
  | zero => show X ∣ (0 : PowerSeries R); exact dvd_zero _
  | succ k ih => show X ∣ T W (seq W k); exact X_dvd_wMap W ih

theorem seq_step (k : ℕ) : X ^ k ∣ seq W (k + 1) - seq W k := by
  induction k with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    show X ^ (k + 1) ∣ T W (seq W (k + 1)) - T W (seq W k)
    exact contract W (X_dvd_seq W _) (X_dvd_seq W _) ih

theorem seq_far (j i : ℕ) : X ^ j ∣ seq W (j + i) - seq W j := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := seq_step W (j + i)
    have h2 : (X : PowerSeries R) ^ j ∣ X ^ (j + i) := pow_dvd_pow X (Nat.le_add_right j i)
    have e : j + (i + 1) = j + i + 1 := by omega
    rw [e, show seq W (j + i + 1) - seq W j
      = (seq W (j + i + 1) - seq W (j + i)) + (seq W (j + i) - seq W j) by ring]
    exact dvd_add (h2.trans h1) ih

def lim : PowerSeries R := PowerSeries.mk fun n => coeff n (seq W (n + 1))

theorem lim_approx (k : ℕ) : X ^ k ∣ lim W - seq W k := by
  rw [X_pow_dvd_iff]
  intro m hm
  obtain ⟨i, rfl⟩ : ∃ i, k = m + 1 + i := ⟨k - (m + 1), by omega⟩
  have h := X_pow_dvd_iff.mp (seq_far W (m + 1) i) m (Nat.lt_succ_self m)
  simp only [map_sub, lim, coeff_mk] at h ⊢
  linear_combination -h

theorem lim_fixed : WFixed W (lim W) := by
  have h1 := lim_approx W 1
  rw [pow_one] at h1
  have hX : X ∣ lim W := by
    have := dvd_add h1 (X_dvd_seq W 1)
    rwa [sub_add_cancel] at this
  refine ⟨X_dvd_iff.mp hX, ?_⟩
  show lim W = T W (lim W)
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_X_pow_dvd
  intro k
  have h2 := lim_approx W (k + 1)
  have h3 : X ^ (k + 1) ∣ T W (seq W k) - T W (lim W) :=
    contract W (X_dvd_seq W k) hX
      (by rw [← neg_sub]; exact dvd_neg.mpr (lim_approx W k))
  have e : lim W - T W (lim W)
      = (lim W - seq W (k + 1)) + (T W (seq W k) - T W (lim W)) := by
    rw [show seq W (k + 1) = T W (seq W k) from rfl]
    ring
  rw [e]
  exact (pow_dvd_pow X (Nat.le_succ k)).trans (dvd_add h2 h3)

theorem fixed_unique {w w' : PowerSeries R} (hw : WFixed W w) (hw' : WFixed W w') : w = w' := by
  have hX : X ∣ w := X_dvd_iff.mpr hw.1
  have hX' : X ∣ w' := X_dvd_iff.mpr hw'.1
  have key : ∀ k, X ^ k ∣ w - w' := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact one_dvd _
    | succ k ih =>
      have h := contract W hX hX' ih
      rwa [show T W w = w from hw.2.symm, show T W w' = w' from hw'.2.symm] at h
  exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd key)

theorem lead {w : PowerSeries R} (hw : WFixed W w) :
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1 := by
  have hX : X ∣ w := X_dvd_iff.mpr hw.1
  have e0 : T W 0 = X ^ 3 := by simp only [T]; ring
  have hw2 : T W w = w := hw.2.symm
  have step : ∀ n, X ^ n ∣ w → X ^ (n + 1) ∣ w - X ^ 3 := by
    intro n h
    have e : w - X ^ 3 = (w - 0) * E W w 0 := by
      rw [← T_sub, e0, hw2]
    rw [e, sub_zero, pow_succ]
    exact mul_dvd_mul h (X_dvd_E W hX (dvd_zero X))
  have hadd : ∀ n, n ≤ 3 → X ^ n ∣ w - X ^ 3 → X ^ n ∣ w := by
    intro n hn h
    have := dvd_add h (pow_dvd_pow (X : PowerSeries R) hn)
    rwa [sub_add_cancel] at this
  have h1 : X ^ 1 ∣ w := by rw [pow_one]; exact hX
  have h2 : X ^ 2 ∣ w := hadd 2 (by norm_num) (step 1 h1)
  have h3 : X ^ 3 ∣ w := hadd 3 le_rfl (step 2 h2)
  have h4 : X ^ 4 ∣ w - X ^ 3 := step 3 h3
  have c := X_pow_dvd_iff.mp h3
  have c4 := X_pow_dvd_iff.mp h4 3 (by norm_num)
  rw [map_sub, coeff_X_pow_self] at c4
  exact ⟨c 0 (by norm_num), c 1 (by norm_num), c 2 (by norm_num), sub_eq_zero.mp c4⟩

end Series

section Subst

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem mv_eq_zero {σ : Type*} {d e : MvPowerSeries σ R}
    (he : MvPowerSeries.constantCoeff e = 0) (h : d = d * e) : d = 0 := by
  have hc : IsUnit (MvPowerSeries.constantCoeff (1 - e)) := by
    rw [map_sub, map_one, he, sub_zero]
    exact isUnit_one
  have hu : IsUnit (1 - e) := MvPowerSeries.isUnit_iff_constantCoeff.mpr hc
  have h0 : d * (1 - e) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  exact hu.mul_left_eq_zero.mp h0

private theorem hasSubst_of_constantCoeff_eq_zero_elliptic_torsion {σ : Type} {s : MvPowerSeries σ R}
    (hs : MvPowerSeries.constantCoeff s = 0) : PowerSeries.HasSubst s :=
  PowerSeries.HasSubst.of_constantCoeff_zero hs

private theorem substAlgHom_apply' {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s)
    (f : PowerSeries R) : PowerSeries.substAlgHom ha f = f.subst s :=
  congrFun (PowerSeries.coe_substAlgHom ha) f

private theorem substAlgHom_X' {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s) :
    PowerSeries.substAlgHom ha (X : PowerSeries R) = s := by
  rw [substAlgHom_apply']
  exact PowerSeries.subst_X ha

private theorem powerSeries_smul_eq_C_mul (r : R) (f : PowerSeries R) : r • f = C r * f :=
  PowerSeries.smul_eq_C_mul f r

private theorem substAlgHom_C {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s)
    (r : R) : PowerSeries.substAlgHom ha (C r) = algebraMap R (MvPowerSeries σ R) r := by
  rw [show (C r : PowerSeries R) = r • (1 : PowerSeries R) by rw [powerSeries_smul_eq_C_mul, mul_one],
    map_smul, map_one, Algebra.smul_def, mul_one]

private theorem constantCoeff_subst_eq_zero_elliptic_torsion {w : PowerSeries R} (hw0 : constantCoeff w = 0)
    {σ : Type} (s : MvPowerSeries σ R) (hs : MvPowerSeries.constantCoeff s = 0) :
    MvPowerSeries.constantCoeff (w.subst s) = 0 := by
  have ha := hasSubst_of_constantCoeff_eq_zero_elliptic_torsion hs
  obtain ⟨w₁, hw₁⟩ := X_dvd_iff.mpr hw0
  rw [← substAlgHom_apply' ha, hw₁, map_mul, substAlgHom_X' ha, map_mul, hs, zero_mul]

theorem subst_eq {w : PowerSeries R} (hw : WFixed W w) {σ : Type} (s : MvPowerSeries σ R)
    (hs : MvPowerSeries.constantCoeff s = 0) : WEqAt W s (w.subst s) := by
  have ha := hasSubst_of_constantCoeff_eq_zero_elliptic_torsion hs
  have e := congrArg (PowerSeries.substAlgHom ha) hw.2
  simp only [map_add, map_mul, map_pow, substAlgHom_C ha, substAlgHom_X' ha] at e
  rw [substAlgHom_apply' ha] at e
  unfold Formalism.ELL.WEqAt
  simp only [Algebra.smul_def]
  linear_combination e

end Subst

end WeierstrassSeriesLimit

open WeierstrassSeriesLimit in
theorem wSeriesExistsUnique_holds : WSeriesUnique.{u} := by
  intro R _ W
  exact ⟨Formalism.ELL.WeierstrassSeriesLimit.lim W, Formalism.ELL.WeierstrassSeriesLimit.lim_fixed W,
    fun w hw => Formalism.ELL.WeierstrassSeriesLimit.fixed_unique W hw (Formalism.ELL.WeierstrassSeriesLimit.lim_fixed W)⟩

open WeierstrassSeriesLimit in
theorem wSeriesLeadingTerm_holds : WSeriesLead.{u} := by
  intro R _ W w hw
  exact Formalism.ELL.WeierstrassSeriesLimit.lead W hw

open WeierstrassSeriesLimit in
theorem wSeriesSubstUnique_holds : WSubstUnique.{u} := by
  intro R _ W w hw σ _ s hs
  refine ⟨Formalism.ELL.WeierstrassSeriesLimit.subst_eq W hw s hs, fun v hv hvE => ?_⟩
  have hu := Formalism.ELL.WeierstrassSeriesLimit.subst_eq W hw s hs
  have hu0 : MvPowerSeries.constantCoeff (w.subst s) = 0 := _root_.Formalism.ELL.WeierstrassSeriesLimit.constantCoeff_subst_eq_zero_elliptic_torsion hw.1 s hs
  unfold WEqAt at hu hvE
  simp only [Algebra.smul_def] at hu hvE
  have key : v - w.subst s = (v - w.subst s) *
      (algebraMap R (MvPowerSeries σ R) W.a₁ * s + algebraMap R (MvPowerSeries σ R) W.a₂ * s ^ 2
        + algebraMap R (MvPowerSeries σ R) W.a₃ * (v + w.subst s)
        + algebraMap R (MvPowerSeries σ R) W.a₄ * s * (v + w.subst s)
        + algebraMap R (MvPowerSeries σ R) W.a₆ * (v ^ 2 + v * w.subst s + w.subst s ^ 2)) := by
    linear_combination hvE - hu
  refine sub_eq_zero.mp (Formalism.ELL.WeierstrassSeriesLimit.mv_eq_zero ?_ key)
  simp [hs, hv, hu0]

end Formalism.ELL
