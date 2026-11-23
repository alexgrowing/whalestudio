import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDefs

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Finset
open scoped ENNReal

theorem cn_lint_prod {a : ℕ} (h : Fin a → ℝ → ℝ) (hi : ∀ i, Integrable (h i)) (h0 : ∀ i t, 0 ≤ h i t) :
    ∫⁻ t : Fin a → ℝ, ENNReal.ofReal (∏ i, h i (t i)) = ENNReal.ofReal (∏ i, ∫ s, h i s) := by
  rw [← integral_fintype_prod_volume_eq_prod]
  refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
  · exact Integrable.fintype_prod hi
  · exact Filter.Eventually.of_forall fun t => Finset.prod_nonneg fun i _ => h0 i (t i)

theorem cn_int_log (f j : ℕ) (ts : ℝ) (h0 : 0 < ts) (h1 : ts ≤ 1 / 2) :
    Integrable ((Set.Ico ts (1 / 2)).indicator fun t : ℝ => 2 * (f : ℝ) * j / t) ∧
      ∫ t, (Set.Ico ts (1 / 2)).indicator (fun t : ℝ => 2 * (f : ℝ) * j / t) t =
        2 * (f : ℝ) * j * Real.log (1 / (2 * ts)) := by
  have hc : ContinuousOn (fun t : ℝ => 2 * (f : ℝ) * j / t) (Set.Icc ts (1 / 2)) :=
    continuousOn_const.div continuousOn_id fun t ht => (lt_of_lt_of_le h0 ht.1).ne'
  have hI : IntegrableOn (fun t : ℝ => 2 * (f : ℝ) * j / t) (Set.Icc ts (1 / 2)) := hc.integrableOn_Icc
  refine ⟨(integrable_indicator_iff measurableSet_Ico).2 (hI.mono_set Set.Ico_subset_Icc_self), ?_⟩
  rw [integral_indicator measurableSet_Ico, ← Formalism.HermitianLatticeCounting.Final.S7.logVolume f j ts h0 h1,
    intervalIntegral.integral_of_le h1, integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

theorem cn_int_tau (f j n0 : ℕ) (hf : 1 ≤ f) (hj : 1 ≤ j) (hn : 1 ≤ n0) :
    Integrable ((Set.Ioo (0 : ℝ) (1 / 2)).indicator fun t : ℝ => t ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / t)) ∧
      ∫ t, (Set.Ioo (0 : ℝ) (1 / 2)).indicator (fun t : ℝ => t ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / t)) t =
        (1 / 2) ^ (2 * j * n0 * f) / (n0 : ℝ) := by
  have hT := Formalism.HermitianLatticeCounting.Final.S7.tauIntegral f j n0 hf hj hn
  have hpos : (0 : ℝ) < (1 / 2) ^ (2 * j * n0 * f) / (n0 : ℝ) := by positivity
  have hII : IntervalIntegrable (fun t : ℝ => t ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / t)) volume 0 (1 / 2) := by
    by_contra hcon
    rw [intervalIntegral.integral_undef hcon] at hT
    exact hpos.ne hT
  have hI : IntegrableOn (fun t : ℝ => t ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / t)) (Set.Ioc 0 (1 / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hII
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).2 (hI.mono_set Set.Ioo_subset_Ioc_self), ?_⟩
  rw [integral_indicator measurableSet_Ioo, ← hT, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]

abbrev cn_Root (a : ℕ) : Type :=
  ({p : Fin a × Fin a // p.1 < p.2} ⊕ {p : Fin a × Fin a // p.1 < p.2}) ⊕ (Fin a ⊕ Fin a)

def cn_la {a : ℕ} (t : Fin a → ℝ) : cn_Root a → ℝ
  | .inl (.inl p) => t p.1.1 / t p.1.2
  | .inl (.inr p) => t p.1.1 * t p.1.2
  | .inr (.inl x) => t x ^ 2
  | .inr (.inr x) => t x

def cn_dim {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) : cn_Root a → ℕ
  | .inl (.inl p) => 2 * j p.1.1 * j p.1.2
  | .inl (.inr p) => 2 * j p.1.1 * j p.1.2
  | .inr (.inl x) => j x ^ 2
  | .inr (.inr x) => 2 * j x * n0

def cn_Reg (a : ℕ) : Set (Fin a → ℝ) := {t | StrictMono t ∧ ∀ x, 0 < t x ∧ t x < 1 / 2}

def cn_dens {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (t : Fin a → ℝ) : ℝ := ∏ r, cn_la t r ^ (cn_dim j n0 r * f)

def cn_cnt {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (de : ℝ) (t : Fin a → ℝ) : ℝ :=
  ∏ r, (1 + 12 * de / cn_la t r) ^ (cn_dim j n0 r * f)

theorem cn_sum_pairs {a : ℕ} (F : Fin a → Fin a → ℕ) :
    ∑ p : {p : Fin a × Fin a // p.1 < p.2}, F p.1.1 p.1.2 = ∑ x, ∑ y with x < y, F x y := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin a × Fin a => p.1 < p.2) (by simp)
    (fun p => F p.1 p.2), Finset.sum_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => (Finset.sum_filter _ _).symm

theorem cn_sum_dim {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) : ∑ r, cn_dim j n0 r = Formalism.HermitianLatticeCounting.S7.dimN j n0 := by
  simp only [Fintype.sum_sum_type, cn_dim, Formalism.HermitianLatticeCounting.S7.dimN]
  rw [cn_sum_pairs fun x y => 2 * j x * j y]
  ring

theorem cn_la_mem {a : ℕ} {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) (r : cn_Root a) : 0 < cn_la t r ∧ cn_la t r < 1 := by
  obtain ⟨hm, hb⟩ := ht
  rcases r with (p | p) | (x | x)
  · have h1 := hb p.1.1
    have h2 := hb p.1.2
    exact ⟨div_pos h1.1 h2.1, (div_lt_one h2.1).2 (hm p.2)⟩
  · have h1 := hb p.1.1
    have h2 := hb p.1.2
    refine ⟨mul_pos h1.1 h2.1, ?_⟩
    show t p.1.1 * t p.1.2 < 1
    nlinarith
  · have h1 := hb x
    refine ⟨pow_pos h1.1 2, ?_⟩
    show t x ^ 2 < 1
    nlinarith
  · have h1 := hb x
    exact ⟨h1.1, by show t x < 1; linarith⟩

theorem cn_cnt_dens_le {a : ℕ} (j : Fin a → ℕ) (n0 f n q : ℕ) (de : ℝ) (hn : n0 + 2 * ∑ x, j x = n) (hq : ∑ x, j x ≤ q)
    (hde : 0 ≤ de) (hsm : de * q * n * f ≤ 1 / 100) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    cn_cnt j n0 f de t * cn_dens j n0 f t ≤ 2 := by
  refine Formalism.HermitianLatticeCounting.Final.S7.nearProduct (cn_Root a) (cn_la t) (cn_dim j n0) n q (∑ x, j x) f de 12 (cn_la_mem ht) hde
    (by norm_num) (by norm_num) ?_ hq hsm
  rw [cn_sum_dim, ← hn]
  exact (Formalism.HermitianLatticeCounting.Final.S7.dimIdentity a j n0).2.1

theorem cn_dens_le {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    cn_dens j n0 f t ≤ ∏ x, t x ^ (2 * j x * n0 * f) := by
  have h1 : ∀ r, 0 ≤ cn_la t r ^ (cn_dim j n0 r * f) ∧ cn_la t r ^ (cn_dim j n0 r * f) ≤ 1 := fun r =>
    ⟨pow_nonneg (cn_la_mem ht r).1.le _, pow_le_one₀ (cn_la_mem ht r).1.le (cn_la_mem ht r).2.le⟩
  unfold cn_dens
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type (f := fun r : Fin a ⊕ Fin a => _)]
  have hA : ∏ r : {p : Fin a × Fin a // p.1 < p.2} ⊕ {p : Fin a × Fin a // p.1 < p.2},
      cn_la t (Sum.inl r) ^ (cn_dim j n0 (Sum.inl r) * f) ≤ 1 :=
    Finset.prod_le_one (fun r _ => (h1 _).1) fun r _ => (h1 _).2
  have hB : ∏ x : Fin a, cn_la t (Sum.inr (Sum.inl x)) ^ (cn_dim j n0 (Sum.inr (Sum.inl x)) * f) ≤ 1 :=
    Finset.prod_le_one (fun r _ => (h1 _).1) fun r _ => (h1 _).2
  have hA0 : 0 ≤ ∏ r : {p : Fin a × Fin a // p.1 < p.2} ⊕ {p : Fin a × Fin a // p.1 < p.2},
      cn_la t (Sum.inl r) ^ (cn_dim j n0 (Sum.inl r) * f) := Finset.prod_nonneg fun r _ => (h1 _).1
  have hB0 : 0 ≤ ∏ x : Fin a, cn_la t (Sum.inr (Sum.inl x)) ^ (cn_dim j n0 (Sum.inr (Sum.inl x)) * f) :=
    Finset.prod_nonneg fun r _ => (h1 _).1
  have hC0 : 0 ≤ ∏ x : Fin a, cn_la t (Sum.inr (Sum.inr x)) ^ (cn_dim j n0 (Sum.inr (Sum.inr x)) * f) :=
    Finset.prod_nonneg fun r _ => (h1 _).1
  have hC : ∏ x : Fin a, cn_la t (Sum.inr (Sum.inr x)) ^ (cn_dim j n0 (Sum.inr (Sum.inr x)) * f) =
      ∏ x, t x ^ (2 * j x * n0 * f) := rfl
  rw [← hC]
  calc _ ≤ 1 * (1 * ∏ x : Fin a, cn_la t (Sum.inr (Sum.inr x)) ^ (cn_dim j n0 (Sum.inr (Sum.inr x)) * f)) := by
        gcongr
    _ = _ := by ring

end Formalism.MainNotions.LeviCoordinates

end
