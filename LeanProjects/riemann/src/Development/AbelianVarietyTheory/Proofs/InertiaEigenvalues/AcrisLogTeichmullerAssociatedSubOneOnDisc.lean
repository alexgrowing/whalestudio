import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTeichmullerTiltMinusOneLeStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

open Filter Topology

namespace GlobalTheory.BSP.SeedT

section Gen

variable (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)

theorem norm_intCast_le (z : ℤ) : ‖(z : Disc l u ρ)‖ ≤ 1 := by
  have := norm_toDisc_le (l := l) (u := u) (ρ := ρ) (z : A)
  rwa [map_intCast] at this

theorem norm_natCast_le (z : ℕ) : ‖(z : Disc l u ρ)‖ ≤ 1 := by
  have := norm_toDisc_le (l := l) (u := u) (ρ := ρ) (z : A)
  rwa [map_natCast] at this

theorem norm_lpow_mul (e : ℕ) (y : Disc l u ρ) : ‖((l : Disc l u ρ)) ^ e * y‖ = ‖y‖ / (l : ℝ) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', mul_assoc, DiscBasic.norm_l_mul l u ρ, ih, pow_succ']
    field_simp

theorem norm_coprime_mul (n : ℕ) (h : Nat.Coprime l n) (x : Disc l u ρ) : ‖(n : Disc l u ρ) * x‖ = ‖x‖ := by
  haveI := DiscBasic.isUltrametricDist_disc l u ρ
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hc := congrArg (Int.cast : ℤ → Disc l u ρ) hab
  push_cast at hc
  have e : x = (a : Disc l u ρ) * ((l : Disc l u ρ) * x) + (b : Disc l u ρ) * ((n : Disc l u ρ) * x) := by
    linear_combination (-x) * hc
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  apply le_antisymm
  · exact (norm_mul_le _ _).trans (by nlinarith [norm_natCast_le l u ρ n, norm_nonneg x])
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : ‖(a : Disc l u ρ) * ((l : Disc l u ρ) * x)‖ ≤ ‖x‖ / l := by
      rw [← DiscBasic.norm_l_mul l u ρ x]
      exact (norm_mul_le _ _).trans (by nlinarith [norm_intCast_le l u ρ a, norm_nonneg ((l : Disc l u ρ) * x)])
    have h2 : ‖(b : Disc l u ρ) * ((n : Disc l u ρ) * x)‖ ≤ ‖(n : Disc l u ρ) * x‖ :=
      (norm_mul_le _ _).trans (by nlinarith [norm_intCast_le l u ρ b, norm_nonneg ((n : Disc l u ρ) * x)])
    have h3 := IsUltrametricDist.norm_add_le_max ((a : Disc l u ρ) * ((l : Disc l u ρ) * x))
      ((b : Disc l u ρ) * ((n : Disc l u ρ) * x))
    rw [← e] at h3
    have h0 := norm_nonneg ((n : Disc l u ρ) * x)
    rcases le_max_iff.1 h3 with h4 | h4
    · have : ‖x‖ ≤ ‖x‖ / l := h4.trans h1
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    · linarith

theorem isUnit_coprime (n : ℕ) (h : Nat.Coprime l n) : IsUnit (n : Disc l u ρ) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hc := congrArg (Int.cast : ℤ → Disc l u ρ) hab
  push_cast at hc
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hn : ‖(a : Disc l u ρ) * (l : Disc l u ρ)‖ < 1 := by
    rw [mul_comm, DiscBasic.norm_l_mul l u ρ, div_lt_one (by linarith)]
    linarith [norm_intCast_le l u ρ a]
  have hu : IsUnit ((b : Disc l u ρ) * (n : Disc l u ρ)) := by
    refine ⟨Units.oneSub _ hn, ?_⟩
    rw [Units.val_oneSub]
    linear_combination -hc
  exact isUnit_of_mul_isUnit_right hu

theorem isUnit_natCast (n : ℕ) (hn : n ≠ 0) : IsUnit (n : Disc l u ρ) := by
  obtain ⟨e, n', hd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  push_cast
  exact ((isUnit_l_disc l u ρ).pow e).mul (isUnit_coprime l u ρ n' ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hd))

theorem norm_le_natCast_mul (n : ℕ) (hn : n ≠ 0) (x : Disc l u ρ) : ‖x‖ ≤ n * ‖(n : Disc l u ρ) * x‖ := by
  obtain ⟨e, n', hd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hn' : n' ≠ 0 := by rintro rfl; simp at hn
  have hle : (l : ℝ) ^ e ≤ ((l ^ e * n' : ℕ) : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ n' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn'
    nlinarith [pow_pos (show (0 : ℝ) < l by exact_mod_cast hl.out.pos) e]
  have hpos : (0 : ℝ) < (l : ℝ) ^ e := pow_pos (by exact_mod_cast hl.out.pos) e
  have key : ‖((l ^ e * n' : ℕ) : Disc l u ρ) * x‖ = ‖x‖ / (l : ℝ) ^ e := by
    push_cast
    rw [mul_assoc, norm_lpow_mul, norm_coprime_mul l u ρ n' ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hd)]
  rw [key]
  calc ‖x‖ = (l : ℝ) ^ e * (‖x‖ / (l : ℝ) ^ e) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)

end Gen

end GlobalTheory.BSP.SeedT

namespace GlobalTheory.BSP.SeedT

theorem gamma_partial {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (μ : Ainf l) (n : ℕ) (s : Per.Acris0 l)
    (hs : ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) μ) ^ (k + 1)) :
    γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      ∑ k ∈ Finset.range n, (-1) ^ k * bk.iA μ ^ (k + 1) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
  set P : Ainf l := ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Ainf l) * μ ^ (k + 1) with hP
  have h1 : ((n.factorial : ℕ) : Per.Acris0 l) * s = algebraMap (Ainf l) (Per.Acris0 l) P := by
    apply Subtype.ext
    change ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) = algebraMap (Ainf l) (Per.AinfP l) P
    rw [hs, hP]
    simp [map_sum, map_mul, map_pow, map_natCast, map_neg, map_one]
  have h2 := congrArg (fun x => γ (algebraMap (Per.Acris0 l) (Per.Acris l) x)) h1
  simp only [map_mul, map_natCast] at h2
  rw [show algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Ainf l) (Per.Acris0 l) P) =
    algebraMap (Ainf l) (Per.Acris l) P from (GlobalTheory.RingIface.tower l P).symm, hγ, hP] at h2
  simp only [map_sum, map_mul, map_pow, map_natCast, map_neg, map_one] at h2
  have hu := isUnit_natCast l (bk.ev X) bk.ρ₀ n.factorial (Nat.factorial_ne_zero n)
  refine hu.mul_left_cancel (h2.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  have hd : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) hk'
  have hv := isUnit_natCast l (bk.ev X) bk.ρ₀ (k + 1) (Nat.succ_ne_zero k)
  have hq : ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀) =
      ((n.factorial : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
    calc ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀)
        = ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀) *
            (((k + 1 : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀)) := by
          rw [Ring.mul_inverse_cancel _ hv, mul_one]
      _ = ((n.factorial / (k + 1) * (k + 1) : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
          push_cast; ring
      _ = _ := by rw [Nat.div_mul_cancel hd]
  rw [hq]
  ring

theorem t_assoc_mu : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l)
    (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) →
    (∀ x, ‖γ x‖ ≤ 1) → Associated (γ C.t) (bk.iA (mu C.ε)) := by
  intro l hl K bk C γ hγ hγn
  haveI := DiscBasic.isUltrametricDist_disc l (bk.ev X) bk.ρ₀
  set m := bk.iA (mu C.ε) with hm_def
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hm : ‖m‖ ≤ 1 / 3 := by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.norm_teichmullerTiltMinusOne_le l K bk C.ε (core_isEps l C)
    by_cases h : l = 2
    · exact (h2 h).trans (by norm_num)
    · have h3 : (3 : ℝ) ≤ l := by
        have := hl.out.two_le
        exact_mod_cast (show 3 ≤ l by omega)
      refine h1.trans ?_
      rw [one_div]
      exact inv_anti₀ (by norm_num) h3
  set f : ℕ → bk.DA bk.ρ₀ := fun k => (-m) ^ (k + 1) * Ring.inverse ((k + 2 : ℕ) : bk.DA bk.ρ₀) with hf_def
  have hf : ∀ k, ‖f k‖ ≤ (2 / 3 : ℝ) ^ (k + 1) := by
    intro k
    have hu := isUnit_natCast l (bk.ev X) bk.ρ₀ (k + 2) (by omega)
    have e : ((k + 2 : ℕ) : bk.DA bk.ρ₀) * f k = (-m) ^ (k + 1) := by
      rw [hf_def, mul_left_comm, Ring.mul_inverse_cancel _ hu, mul_one]
    have h1 := norm_le_natCast_mul l (bk.ev X) bk.ρ₀ (k + 2) (by omega) (f k)
    rw [e] at h1
    have h2 : ‖(-m) ^ (k + 1)‖ ≤ ‖m‖ ^ (k + 1) := by
      rw [← norm_neg m]; exact norm_pow_le' _ (Nat.succ_pos k)
    have h3 : ‖m‖ ^ (k + 1) ≤ (1 / 3 : ℝ) ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) hm _
    have h4 : ((k + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      have : k + 2 ≤ 2 ^ (k + 1) := Nat.lt_two_pow_self
      exact_mod_cast this
    calc ‖f k‖ ≤ ((k + 2 : ℕ) : ℝ) * ‖(-m) ^ (k + 1)‖ := h1
      _ ≤ (2 : ℝ) ^ (k + 1) * (1 / 3 : ℝ) ^ (k + 1) :=
          mul_le_mul h4 (h2.trans h3) (norm_nonneg _) (by positivity)
      _ = (2 / 3 : ℝ) ^ (k + 1) := by rw [← mul_pow]; norm_num
  have hsum : Summable f := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (2 / 3 : ℝ) < 1)).mul_left (2 / 3)) fun k => ?_
    rw [← pow_succ']
    exact hf k
  set y := ∑' k, f k with hy_def
  have hy : ‖y‖ ≤ 2 / 3 :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun k =>
      (hf k).trans (pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero k))
  have hunit : IsUnit (1 + y) := by
    refine ⟨Units.oneSub (-y) (by rw [norm_neg]; linarith), ?_⟩
    rw [Units.val_oneSub, sub_neg_eq_add]
  set S : ℕ → bk.DA bk.ρ₀ := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * m ^ (k + 1) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) with hS_def
  have hS : ∀ n, S (n + 1) = m * (1 + ∑ k ∈ Finset.range n, f k) := by
    intro n
    induction n with
    | zero => simp [hS_def]
    | succ n ih =>
      have e1 : S (n + 1 + 1) = S (n + 1) + (-1) ^ (n + 1) * m ^ (n + 1 + 1) *
          Ring.inverse ((n + 1 + 1 : ℕ) : bk.DA bk.ρ₀) := by
        simp only [hS_def]; rw [Finset.sum_range_succ]
      rw [e1, ih, Finset.sum_range_succ, hf_def]
      simp only
      rw [neg_pow]
      ring
  have hlim1 : Tendsto (fun n => S (n + 1)) atTop (𝓝 (m * (1 + y))) := by
    simp_rw [hS]
    exact (tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat).const_mul m
  have hlim2 : Tendsto (fun n => S (n + 1)) atTop (𝓝 (γ C.t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε hlinv
    obtain ⟨N, hN⟩ := C.t_log r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨s, hs1, z, hz⟩ := hN (n + 1) (by omega)
    have key := gamma_partial bk γ hγ (mu C.ε) (n + 1) s hs1
    rw [dist_eq_norm, norm_sub_rev]
    have e2 : γ C.t - S (n + 1) = (l : bk.DA bk.ρ₀) ^ r * γ z := by
      rw [hS_def]
      simp only
      rw [← key, ← map_sub, hz, map_mul, map_pow, map_natCast]
    rw [e2, norm_lpow_mul]
    calc ‖γ z‖ / (l : ℝ) ^ r ≤ 1 / (l : ℝ) ^ r :=
          div_le_div_of_nonneg_right (hγn z) (by positivity)
      _ = (l : ℝ)⁻¹ ^ r := by rw [inv_pow, one_div]
      _ < ε := hr
  have heq : γ C.t = m * (1 + y) := tendsto_nhds_unique hlim2 hlim1
  refine ⟨hunit.unit⁻¹, ?_⟩
  rw [heq, mul_assoc, IsUnit.mul_val_inv, mul_one]

end GlobalTheory.BSP.SeedT
