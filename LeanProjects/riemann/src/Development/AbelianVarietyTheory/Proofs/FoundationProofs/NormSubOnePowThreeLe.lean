import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsDirichletCharacterSmoothed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapPadicIntQbarContinuous

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory.AmiceDist

variable {l : ℕ} [Fact l.Prime]

theorem sum_level (μ : ∀ r : ℕ, ZMod (l ^ r) → Qbar l)
    (hμ : ∀ r (x : ZMod (l ^ r)), μ r x = ∑ x' ∈ Finset.univ.filter
      (fun x' : ZMod (l ^ (r + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x), μ (r + 1) x')
    {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) (R : ℕ) (hR : r ≤ R) :
    ∑ x : ZMod (l ^ R), μ R x * z ^ x.val = ∑ x : ZMod (l ^ r), μ r x * z ^ x.val := by
  induction R, hR using Nat.le_induction with
  | base => rfl
  | succ R hR ih =>
    rw [← ih]
    have hzR : z ^ (l ^ R) = 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hR
      rw [pow_add, pow_mul, hz, one_pow]
    rw [← Finset.sum_fiberwise Finset.univ
      (fun x' : ZMod (l ^ (R + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ R)) (ZMod (l ^ R)) x')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hμ R x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    rw [← (Finset.mem_filter.1 hx').2, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
      ← pow_eq_pow_mod _ hzR]

theorem norm_trunc_binomial {w : Qbar l} (hw : ‖w‖ ≤ 1) (N k : ℕ) :
    ‖∑ n ∈ Finset.range N, (k.choose n : Qbar l) * w ^ n - (w + 1) ^ k‖ ≤ ‖w‖ ^ N := by
  have h1 : (w + 1) ^ k = ∑ n ∈ Finset.range (N + (k + 1)), (k.choose n : Qbar l) * w ^ n := by
    rw [add_pow]
    simp only [one_pow, mul_one]
    simp_rw [mul_comm (w ^ _)]
    refine Finset.sum_subset (Finset.range_mono (Nat.le_add_left _ _)) fun n _ hn => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hn)]
    simp
  rw [h1, Finset.sum_range_add, sub_add_cancel_left, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hw (Nat.le_add_right _ _))

theorem norm_sub_one_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) : ‖z - 1‖ ≤ 1 := by
  have h : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h1
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  simp [h]

theorem norm_sub_one_pow_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) : ‖z - 1‖ ^ (l ^ r) ≤ ‖((l : ℕ) : Qbar l)‖ := by
  have hw := norm_sub_one_le hz
  have h := (Commute.all (z - 1) 1).add_pow_prime_pow_eq (Fact.out : l.Prime) r
  rw [sub_add_cancel, hz] at h
  simp only [one_pow, mul_one] at h
  have h2 : (z - 1) ^ (l ^ r) = -((l : Qbar l) * (z - 1) *
      ∑ k ∈ Finset.Ioo 0 (l ^ r), (z - 1) ^ (k - 1) * (((l ^ r).choose k / l : ℕ) : Qbar l)) := by
    linear_combination -h
  rw [← norm_pow, h2, norm_neg, norm_mul, norm_mul]
  have h3 : ‖∑ k ∈ Finset.Ioo 0 (l ^ r), (z - 1) ^ (k - 1) * (((l ^ r).choose k / l : ℕ) : Qbar l)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hw) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  calc _ ≤ ‖((l : ℕ) : Qbar l)‖ * 1 * 1 := by gcongr
    _ = _ := by ring

theorem norm_sub_one_pow_three_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) :
    ‖z - 1‖ ^ (l ^ (3 * r)) ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  rw [show 3 * r = r + 2 * r by ring, pow_add, pow_mul, norm_pow]
  refine (pow_le_pow_left₀ (by positivity) (norm_sub_one_pow_le hz) _).trans ?_
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le

theorem amice : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (μ : ∀ r : ℕ, ZMod (l ^ r) → Qbar l), (∀ r x, μ r x ∈ c.O) →
    (∀ r (x : ZMod (l ^ r)), μ r x = ∑ x' ∈ Finset.univ.filter
      (fun x' : ZMod (l ^ (r + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x), μ (r + 1) x') →
    ∃ L : PowerSeries (Qbar l), (∀ n, L.coeff n ∈ c.O) ∧ ∀ r, 1 ≤ r → ∀ z : Qbar l, z ^ (l ^ r) = 1 →
      Cg (2 * r) (tval L (l ^ (3 * r)) z) (∑ x : ZMod (l ^ r), μ r x * z ^ x.val) := by
  intro l _ c μ hO hμ
  let a : ℕ → ℕ → Qbar l := fun n R => ∑ x : ZMod (l ^ R), μ R x * (x.val.choose n : Qbar l)
  have ha : ∀ n R, a n R ∈ c.O := fun n R => sum_mem fun x _ => mul_mem (hO R x) (natCast_mem _ _)
  have hlim : ∀ n, ∃ b ∈ c.O, Filter.Tendsto (a n) (Filter.hyperfilter ℕ) (nhds b) := by
    intro n
    obtain ⟨b, hb, h⟩ := (GlobalTheory.Coef.isCompact_O l c).ultrafilter_le_nhds ((Filter.hyperfilter ℕ).map (a n))
      (by
        rw [Filter.le_principal_iff]
        exact Filter.mem_map.2 (Filter.univ_mem' fun R => ha n R))
    exact ⟨b, hb, h⟩
  choose b hb hab using hlim
  refine ⟨PowerSeries.mk b, fun n => by simpa using hb n, fun r _ z hz => ?_⟩
  unfold Cg tval
  simp only [PowerSeries.coeff_mk]
  have ht : Filter.Tendsto (fun R => ‖∑ n ∈ Finset.range (l ^ (3 * r)), a n R * (z - 1) ^ n -
      ∑ x : ZMod (l ^ r), μ r x * z ^ x.val‖) (Filter.hyperfilter ℕ)
      (nhds ‖∑ n ∈ Finset.range (l ^ (3 * r)), b n * (z - 1) ^ n - ∑ x : ZMod (l ^ r), μ r x * z ^ x.val‖) :=
    ((tendsto_finset_sum _ fun n _ => (hab n).mul_const _).sub_const _).norm
  refine le_of_tendsto ht ?_
  have hev : ∀ᶠ R in (Filter.hyperfilter ℕ : Filter ℕ), r ≤ R :=
    Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop r)
  filter_upwards [hev] with R hR
  rw [← sum_level μ hμ hz R hR]
  simp only [a, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (FirstDer.norm_le_one_of_mem c (hO R x))).trans ?_
  have h := norm_trunc_binomial (norm_sub_one_le hz) (l ^ (3 * r)) x.val
  rw [sub_add_cancel] at h
  exact h.trans (norm_sub_one_pow_three_le hz)

end GlobalTheory.AmiceDist
