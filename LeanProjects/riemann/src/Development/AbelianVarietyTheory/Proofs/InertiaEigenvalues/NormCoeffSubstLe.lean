import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero

noncomputable section

namespace GlobalTheory.HWL.ExpSub

open PowerSeries Filter Topology

section General

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def Ex (u a e : K⟦X⟧) : Prop :=
  ∀ k : ℕ, Tendsto (fun m : ℕ => coeff k (Polynomial.aeval u (trunc m a))) atTop (𝓝 (coeff k e))

theorem pow_bound (u : K⟦X⟧) (k : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (h : ∀ j ≤ k, ‖coeff j u‖ * ρ ^ j ≤ r) (n : ℕ) : ∀ j ≤ k, ‖coeff j (u ^ n)‖ * ρ ^ j ≤ r ^ n := by
  induction n with
  | zero =>
    intro j _
    rw [pow_zero, pow_zero, coeff_one]
    split_ifs with hj
    · simp [hj]
    · simp
  | succ n ih =>
    intro j hj
    rw [pow_succ, coeff_mul, ← le_div_iff₀ (pow_pos hρ j)]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    rw [le_div_iff₀ (pow_pos hρ j), norm_mul, ← hp', pow_add, mul_mul_mul_comm, pow_succ]
    exact mul_le_mul (ih _ (by omega)) (h _ (by omega)) (by positivity) (by positivity)

theorem exists_bound (u : K⟦X⟧) (hu : ‖constantCoeff u‖ < 1) (k : ℕ) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ 0 < C ∧ ∀ (p : Polynomial K) (B : ℝ), 0 ≤ B →
      (∀ m, ‖p.coeff m‖ * r ^ m ≤ B) → ‖coeff k (Polynomial.aeval u p)‖ ≤ C * B := by
  obtain ⟨r, hr0, hr1⟩ := exists_between hu
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr0
  have hev : ∀ᶠ ρ : ℝ in 𝓝[>] 0, ∀ j ∈ Finset.range (k + 1), ‖coeff j u‖ * ρ ^ j < r := by
    rw [eventually_all_finset]
    intro j _
    refine nhdsWithin_le_nhds ?_
    refine ContinuousAt.eventually_lt (f := fun ρ : ℝ => ‖coeff j u‖ * ρ ^ j) (g := fun _ => r)
      (by fun_prop) (by fun_prop) ?_
    rcases j with _ | j
    · simpa using hr0
    · simpa using hr
  obtain ⟨ρ, hρ, hρ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hρ0 : 0 < ρ := hρ0
  have hb := pow_bound u k hρ0 hr.le (fun j hj => (hρ j (Finset.mem_range.2 (by omega))).le)
  refine ⟨r, (ρ ^ k)⁻¹, hr, hr1, by positivity, fun p B hB hp => ?_⟩
  rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n _ => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul, le_inv_mul_iff₀ (pow_pos hρ0 k)]
  calc ρ ^ k * (‖p.coeff n‖ * ‖coeff k (u ^ n)‖) = ‖p.coeff n‖ * (‖coeff k (u ^ n)‖ * ρ ^ k) := by ring
    _ ≤ ‖p.coeff n‖ * r ^ n := mul_le_mul_of_nonneg_left (hb n k le_rfl) (norm_nonneg _)
    _ ≤ B := hp n

theorem coeff_mul_le {f g : K⟦X⟧} (hf : ∀ m, ‖coeff m f‖ ≤ 1) (hg : ∀ m, ‖coeff m g‖ ≤ 1) (m : ℕ) :
    ‖coeff m (f * g)‖ ≤ 1 := by
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem coeff_pow_le {f : K⟦X⟧} (hf : ∀ m, ‖coeff m f‖ ≤ 1) (n m : ℕ) : ‖coeff m (f ^ n)‖ ≤ 1 := by
  simpa using pow_bound f m one_pos zero_le_one (fun j _ => by simpa using hf j) n m le_rfl

theorem Ex.mul {u f g e e' : K⟦X⟧} (hu : ‖constantCoeff u‖ < 1) (hf : ∀ m, ‖coeff m f‖ ≤ 1)
    (hg : ∀ m, ‖coeff m g‖ ≤ 1) (he : Ex u f e) (he' : Ex u g e') : Ex u (f * g) (e * e') := by
  intro k
  obtain ⟨r, C, hr0, hr1, hC, hb⟩ := exists_bound u hu k
  have h1 : Tendsto (fun m : ℕ => coeff k (Polynomial.aeval u (trunc m f * trunc m g))) atTop
      (𝓝 (coeff k (e * e'))) := by
    simp only [map_mul, coeff_mul]
    exact tendsto_finset_sum _ fun p _ => (he _).mul (he' _)
  have h2 : Tendsto (fun m : ℕ => coeff k (Polynomial.aeval u (trunc m (f * g) - trunc m f * trunc m g)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun m => C * r ^ m) (fun M => hb _ _ (by positivity) fun m => ?_) ?_
    · by_cases hm : m < M
      · have : (trunc M (f * g) - trunc M f * trunc M g).coeff m = 0 := by
          rw [Polynomial.coeff_sub, Polynomial.coeff_mul, coeff_trunc, if_pos hm, coeff_mul, sub_eq_zero]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
          rw [coeff_trunc, coeff_trunc, if_pos (by omega), if_pos (by omega)]
        rw [this]; simp [pow_nonneg hr0.le]
      · have : ‖(trunc M (f * g) - trunc M f * trunc M g).coeff m‖ ≤ 1 := by
          rw [Polynomial.coeff_sub, coeff_trunc, if_neg hm, zero_sub, norm_neg, ← Polynomial.coeff_coe,
            Polynomial.coe_mul]
          refine coeff_mul_le (fun j => ?_) (fun j => ?_) m <;>
          · rw [Polynomial.coeff_coe, coeff_trunc]
            split_ifs
            · first | exact hf j | exact hg j
            · simp
        calc _ ≤ 1 * r ^ m := mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ r ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul C
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr fun m => ?_
  rw [← map_add, ← map_add, add_sub_cancel]

theorem Ex.aeval {u f e : K⟦X⟧} (hu : ‖constantCoeff u‖ < 1) (hf : ∀ m, ‖coeff m f‖ ≤ 1)
    (he : Ex u f e) (p : Polynomial K) : Ex u (Polynomial.aeval f p) (Polynomial.aeval e p) := by
  have hpow : ∀ n : ℕ, Ex u (f ^ n) (e ^ n) := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [← tendsto_add_atTop_iff_nat 1]
      simp
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hu (coeff_pow_le hf n) hf he
  intro k
  simp only [Polynomial.aeval_eq_sum_range (p := p), map_sum, map_smul]
  exact tendsto_finset_sum _ fun n _ => (hpow n k).const_smul _

theorem Ex.of_approx {u f e : K⟦X⟧} (hu : ‖constantCoeff u‖ < 1) (F E : ℕ → K⟦X⟧)
    (h : ∀ N, Ex u (F N) (E N)) (hE : ∀ k, Tendsto (fun N => coeff k (E N)) atTop (𝓝 (coeff k e)))
    (hF : ∀ r : ℝ, 0 < r → r < 1 → ∀ ε > 0, ∀ᶠ N in atTop, ∀ m, ‖coeff m (f - F N)‖ * r ^ m ≤ ε) :
    Ex u f e := by
  intro k
  obtain ⟨r, C, hr0, hr1, hC, hb⟩ := exists_bound u hu k
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨N, hN1, hN2⟩ := ((hF r hr0 hr1 (ε / 3 / C) (by positivity)).and
    (Metric.tendsto_nhds.1 (hE k) _ hε3)).exists
  filter_upwards [Metric.tendsto_nhds.1 (h N k) _ hε3] with M hM
  have h3 := hb (trunc M (f - F N)) (ε / 3 / C) (by positivity) fun m => by
    rw [coeff_trunc]
    split_ifs
    · exact hN1 m
    · simp; positivity
  rw [map_sub, map_sub, map_sub, ← dist_eq_norm, mul_div_cancel₀ _ hC.ne'] at h3
  have := dist_triangle4 (coeff k (Polynomial.aeval u (trunc M f)))
    (coeff k (Polynomial.aeval u (trunc M (F N)))) (coeff k (E N)) (coeff k e)
  linarith

theorem norm_coeff_subst_le {Y : K⟦X⟧} (h0 : constantCoeff Y = 0) (hY : ∀ m, ‖coeff m Y‖ ≤ 1)
    (a : K⟦X⟧) (m : ℕ) {B : ℝ} (hB : 0 ≤ B) (ha : ∀ n ≤ m, ‖coeff n a‖ ≤ B) :
    ‖coeff m (subst Y a)‖ ≤ B := by
  have hs : HasSubst Y := HasSubst.of_constantCoeff_zero' h0
  rw [coeff_subst' hs, finsum_eq_sum_of_support_subset (s := Finset.range (m + 1))]
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB fun n hn => ?_
    rw [smul_eq_mul, norm_mul]
    calc _ ≤ B * 1 := mul_le_mul (ha n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))) (coeff_pow_le hY n m)
          (norm_nonneg _) hB
      _ = B := mul_one B
  · intro n hn
    by_contra hlt
    apply hn
    have hlt' : m < n := by simpa using hlt
    have : X ^ n ∣ Y ^ n := pow_dvd_pow_of_dvd (X_dvd_iff.2 h0) n
    simp [X_pow_dvd_iff.1 this m hlt']

theorem weighted_subst_le {Y : K⟦X⟧} (h0 : constantCoeff Y = 0) (hY : ∀ m, ‖coeff m Y‖ ≤ 1)
    (a : K⟦X⟧) {r B : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ha : ∀ n, ‖coeff n a‖ * r ^ n ≤ B) (m : ℕ) :
    ‖coeff m (subst Y a)‖ * r ^ m ≤ B := by
  have hB : 0 ≤ B := le_trans (by positivity) (ha 0)
  rw [← le_div_iff₀ (pow_pos hr0 m)]
  refine norm_coeff_subst_le h0 hY a m (by positivity) fun n hn => ?_
  rw [le_div_iff₀ (pow_pos hr0 m)]
  exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hn) (norm_nonneg _)) (ha n)

theorem conv_subst {Y : K⟦X⟧} (h0 : constantCoeff Y = 0) (hY : ∀ m, ‖coeff m Y‖ ≤ 1) (a : K⟦X⟧)
    (ha : ∀ r : ℝ, 0 < r → r < 1 → Tendsto (fun k : ℕ => ‖coeff k a‖ * r ^ k) atTop (𝓝 0))
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun k : ℕ => ‖coeff k (subst Y a)‖ * r ^ k) atTop (𝓝 0) := by
  obtain ⟨s, hs0, hs1⟩ := exists_between hr1
  have hs : 0 < s := hr0.trans hs0
  obtain ⟨B, hB⟩ := (ha s hs hs1).bddAbove_range
  have hb := weighted_subst_le h0 hY a hs hs1 (B := B) fun n => hB ⟨n, rfl⟩
  refine squeeze_zero (g := fun k => B * (r / s) ^ k) (fun k => by positivity) (fun k => ?_) ?_
  · calc _ = (‖coeff k (subst Y a)‖ * s ^ k) * (r / s) ^ k := by
          rw [div_pow]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb k) (by positivity)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((div_lt_one hs).2 hs0)).const_mul B

theorem Ex.subst {u v Y a e : K⟦X⟧} (hu : ‖constantCoeff u‖ < 1) (h0 : constantCoeff Y = 0)
    (hY : ∀ m, ‖coeff m Y‖ ≤ 1) (hv : Ex u Y v)
    (ha : ∀ r : ℝ, 0 < r → r < 1 → Tendsto (fun k : ℕ => ‖coeff k a‖ * r ^ k) atTop (𝓝 0))
    (he : Ex v a e) : Ex u (PowerSeries.subst Y a) e := by
  have hs : HasSubst Y := HasSubst.of_constantCoeff_zero' h0
  refine Ex.of_approx hu _ _ (fun N => Ex.aeval hu hY hv (trunc N a)) he fun r hr0 hr1 ε hε => ?_
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((ha r hr0 hr1).eventually (ge_mem_nhds hε))
  filter_upwards [eventually_ge_atTop N₀] with N hN m
  rw [← subst_coe hs, ← subst_sub hs]
  refine weighted_subst_le h0 hY _ hr0 hr1 (fun n => ?_) m
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc]
  split_ifs with hn
  · simpa using hε.le
  · rw [sub_zero]; exact hN₀ n (by omega)

theorem Ex.rescale {v a e : K⟦X⟧} (c : K) (he : Ex v a e) :
    Ex (PowerSeries.rescale c v) a (PowerSeries.rescale c e) := by
  intro k
  have : ∀ p : Polynomial K, Polynomial.aeval (PowerSeries.rescale c v) p =
      PowerSeries.rescale c (Polynomial.aeval v p) := fun p => by
    simp only [Polynomial.aeval_eq_sum_range (p := p), map_sum, ← map_pow]
    refine Finset.sum_congr rfl fun n _ => ?_
    ext j
    simp only [coeff_rescale, coeff_smul, smul_eq_mul, mul_left_comm]
  simp only [this, coeff_rescale]
  exact (he k).const_mul _

end General

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

open PowerSeries Filter Topology in
open TensorProduct in
private lemma norm_le_one_of_mem_integralClosure_padicInt {l : ℕ} [Fact (Nat.Prime l)] {LL : _root_.Formalism.BasicNotions.Loc.FinExt l}
    (x : ↥LL.1) (hx : x ∈ integralClosure ℤ_[l] ↥LL.1) : ‖x‖ ≤ 1 := by
  have hc : ∀ c : ℤ_[l], ‖algebraMap ℤ_[l] ↥LL.1 c‖ ≤ 1 := by
    intro c
    have h : ((algebraMap ℤ_[l] ↥LL.1 c : ↥LL.1) : PadicAlgCl l) = ((c : ℚ_[l]) : PadicAlgCl l) := rfl
    show ‖((algebraMap ℤ_[l] ↥LL.1 c : ↥LL.1) : PadicAlgCl l)‖ ≤ 1
    rw [h, PadicAlgCl.norm_extends]
    exact PadicInt.norm_le_one c
  by_contra hlt
  push_neg at hlt
  obtain ⟨p, hpm, hp⟩ := hx
  have hsum : x ^ p.natDegree =
      -∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] ↥LL.1 (p.coeff i) * x ^ i := by
    have h := hp
    rw [hpm.as_sum] at h
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
    exact eq_neg_of_add_eq_zero_left h
  have hn : p.natDegree ≠ 0 := by
    intro h0
    rw [h0] at hsum
    simp at hsum
  have hle : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1) := by
    rw [← norm_pow, hsum, norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    calc ‖algebraMap ℤ_[l] ↥LL.1 (p.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (p.natDegree - 1) :=
          mul_le_mul (hc _) (pow_le_pow_right₀ hlt.le (by omega)) (by positivity) zero_le_one
      _ = _ := one_mul _
  have := pow_lt_pow_right₀ hlt (show p.natDegree - 1 < p.natDegree by omega)
  linarith

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma rescale_C_eq_C (c b : K) : rescale c (C b) = C b := by
  ext j
  rw [coeff_rescale]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · simp [coeff_C, hj.ne']

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma aeval_rescale_eq_rescale_aeval (c : K) (v : K⟦X⟧) (p : Polynomial K) :
    Polynomial.aeval (rescale c v) p = rescale c (Polynomial.aeval v p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | monomial n b =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    ext j
    rw [coeff_rescale]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · simp [coeff_C, hj.ne']

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma ex_rescale {v a e : K⟦X⟧} (c : K) (he : _root_.GlobalTheory.HWL.ExpSub.Ex v a e) :
    _root_.GlobalTheory.HWL.ExpSub.Ex (rescale c v) a (rescale c e) := by
  intro k
  simp_rw [aeval_rescale_eq_rescale_aeval, coeff_rescale]
  exact (he k).const_mul _

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma exists_norm_coeff_pow_le_mul_pow_sub (u : K⟦X⟧) {r : ℝ} (hr : ‖constantCoeff u‖ ≤ r) (hr1 : r ≤ 1) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, ‖coeff k (u ^ j)‖ ≤ B * r ^ (j - k) := by
  set w : K⟦X⟧ := u - C (constantCoeff u) with hw
  have hw0 : constantCoeff w = 0 := by simp [hw]
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  refine ⟨∑ i ∈ Finset.range (k + 1), ‖coeff k (w ^ i)‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun j => ?_⟩
  have hu : u = w + C (constantCoeff u) := by simp [hw]
  rw [hu, add_pow, map_sum]
  calc ‖∑ i ∈ Finset.range (j + 1), coeff k (w ^ i * C (constantCoeff u) ^ (j - i) * (j.choose i : K⟦X⟧))‖
      ≤ ∑ i ∈ Finset.range (j + 1), ‖coeff k (w ^ i * C (constantCoeff u) ^ (j - i) * (j.choose i : K⟦X⟧))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (if i ≤ k then ‖coeff k (w ^ i)‖ * r ^ (j - k) else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        have hterm : coeff k (w ^ i * C (constantCoeff u) ^ (j - i) * (j.choose i : K⟦X⟧)) =
            (constantCoeff u) ^ (j - i) * (j.choose i : K) * coeff k (w ^ i) := by
          rw [← map_pow, ← map_natCast (C (R := K)), mul_assoc, ← map_mul, mul_comm, coeff_C_mul]
        rw [hterm, norm_mul, norm_mul, norm_pow]
        split_ifs with hik
        · have h1 : ‖constantCoeff u‖ ^ (j - i) ≤ r ^ (j - k) :=
            (pow_le_pow_left₀ (norm_nonneg _) hr _).trans (pow_le_pow_of_le_one hr0 hr1 (by omega))
          have h2 : ‖(j.choose i : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
          calc ‖constantCoeff u‖ ^ (j - i) * ‖(j.choose i : K)‖ * ‖coeff k (w ^ i)‖
              ≤ r ^ (j - k) * 1 * ‖coeff k (w ^ i)‖ := by gcongr
            _ = _ := by ring
        · have : coeff k (w ^ i) = 0 := by
            obtain ⟨w', hw'⟩ := (PowerSeries.X_dvd_iff).mpr hw0
            rw [hw', mul_pow, coeff_X_pow_mul', if_neg (by omega)]
          simp [this]
    _ ≤ ∑ i ∈ Finset.range (k + 1), ‖coeff k (w ^ i)‖ * r ^ (j - k) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          omega
        · intros; positivity
    _ = _ := by rw [Finset.sum_mul]

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma exists_norm_coeff_aeval_le_mul_of_weighted_bound (u : K⟦X⟧) {r : ℝ} (hr : ‖constantCoeff u‖ ≤ r) (hr0 : 0 < r)
    (hr1 : r ≤ 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Polynomial K) (ε : ℝ), 0 ≤ ε → (∀ j, ‖p.coeff j‖ * r ^ j ≤ ε) →
      ‖coeff k (Polynomial.aeval u p)‖ ≤ C * ε := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_coeff_pow_le_mul_pow_sub u hr hr1 k
  refine ⟨B / r ^ k, by positivity, fun p ε hε hp => ?_⟩
  rw [Polynomial.aeval_eq_sum_range, map_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro j _
  rw [PowerSeries.coeff_smul, smul_eq_mul, norm_mul]
  have hpow : r ^ (j - k) * r ^ k ≤ r ^ j := by
    rcases le_or_gt k j with hkj | hkj
    · rw [pow_sub_mul_pow r hkj]
    · rw [Nat.sub_eq_zero_of_le hkj.le, pow_zero, one_mul]
      exact pow_le_pow_of_le_one hr0.le hr1 hkj.le
  calc ‖p.coeff j‖ * ‖coeff k (u ^ j)‖ ≤ ‖p.coeff j‖ * (B * r ^ (j - k)) := by gcongr; exact hB j
    _ = B / r ^ k * (‖p.coeff j‖ * (r ^ (j - k) * r ^ k)) := by field_simp
    _ ≤ B / r ^ k * (‖p.coeff j‖ * r ^ j) := by gcongr
    _ ≤ B / r ^ k * ε := by gcongr; exact hp j

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma ex_add_inertia_eigenvalues {u f g e e' : K⟦X⟧} (h₁ : _root_.GlobalTheory.HWL.ExpSub.Ex u f e)
    (h₂ : _root_.GlobalTheory.HWL.ExpSub.Ex u g e') : _root_.GlobalTheory.HWL.ExpSub.Ex u (f + g) (e + e') := by
  intro k
  simp_rw [map_add]
  exact (h₁ k).add (h₂ k)

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma ex_C_mul {u f e : K⟦X⟧} (a : K) (h : _root_.GlobalTheory.HWL.ExpSub.Ex u f e) :
    _root_.GlobalTheory.HWL.ExpSub.Ex u (C a * f) (C a * e) := by
  intro k
  have hk : ∀ m, coeff k (Polynomial.aeval u (trunc m (C a * f))) =
      a * coeff k (Polynomial.aeval u (trunc m f)) := by
    intro m
    rw [trunc_C_mul, map_mul, Polynomial.aeval_C]
    exact coeff_C_mul _ _ _
  simp_rw [hk, coeff_C_mul]
  exact (h k).const_mul a

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma ex_one' (u : K⟦X⟧) : _root_.GlobalTheory.HWL.ExpSub.Ex u 1 1 := by
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [trunc_one, Polynomial.aeval_one]

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma ex_mul_of_bounded_coeff {u f g e e' : K⟦X⟧} (hu : ‖constantCoeff u‖ < 1) {M : ℝ}
    (hf : ∀ j, ‖coeff j f‖ ≤ M) (hg : ∀ j, ‖coeff j g‖ ≤ M)
    (h₁ : _root_.GlobalTheory.HWL.ExpSub.Ex u f e) (h₂ : _root_.GlobalTheory.HWL.ExpSub.Ex u g e') :
    _root_.GlobalTheory.HWL.ExpSub.Ex u (f * g) (e * e') := by
  intro k
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf 0)
  set r : ℝ := max ‖constantCoeff u‖ (1 / 2) with hr
  have hr0 : 0 < r := lt_max_of_lt_right (by norm_num)
  have hr1 : r < 1 := max_lt hu (by norm_num)
  obtain ⟨Cb, hC0, hC⟩ := exists_norm_coeff_aeval_le_mul_of_weighted_bound u (le_max_left _ _) hr0 hr1.le k
  set D : ℕ → Polynomial K := fun m => trunc m (f * g) - trunc m f * trunc m g with hD
  have hsplit : ∀ m, coeff k (Polynomial.aeval u (trunc m (f * g))) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, coeff x.1 (Polynomial.aeval u (trunc m f)) *
        coeff x.2 (Polynomial.aeval u (trunc m g)) + coeff k (Polynomial.aeval u (D m)) := by
    intro m
    simp only [hD, map_sub, map_mul, coeff_mul]
    ring
  have hD0 : Tendsto (fun m => coeff k (Polynomial.aeval u (D m))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun m : ℕ => Cb * (M * M * r ^ m)) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul (M * M)).const_mul Cb
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => hC (D m) _ (by positivity) (fun j => ?_)) hlim
    simp only [hD, Polynomial.coeff_sub, Polynomial.coeff_mul, coeff_trunc]
    rcases lt_or_ge j m with hjm | hjm
    · have hx : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal j, (if x.1 < m then coeff x.1 f else 0) *
          (if x.2 < m then coeff x.2 g else 0) = coeff x.1 f * coeff x.2 g := by
        intro x hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [if_pos (by omega), if_pos (by omega)]
      rw [if_pos hjm, Finset.sum_congr rfl hx, ← coeff_mul, sub_self, norm_zero, zero_mul]
      positivity
    · rw [if_neg (by omega), zero_sub, norm_neg]
      have hs : ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal j, (if x.1 < m then coeff x.1 f else 0) *
          (if x.2 < m then coeff x.2 g else 0)‖ ≤ M * M := by
        apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
        intro x _
        rw [norm_mul]
        apply mul_le_mul _ _ (norm_nonneg _) hM <;> split_ifs <;> simp [hf, hg, hM]
      calc _ ≤ M * M * r ^ j := by gcongr
        _ ≤ M * M * r ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hjm) (by positivity)
  have hlim := (tendsto_finset_sum (Finset.HasAntidiagonal.antidiagonal k : Finset (ℕ × ℕ))
    fun (x : ℕ × ℕ) _ => (h₁ x.1).mul (h₂ x.2)).add hD0
  rw [add_zero, ← coeff_mul] at hlim
  exact hlim.congr (fun m => (hsplit m).symm)

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_coeff_pow_le_one_of_norm_coeff_le_one {f : K⟦X⟧} (hf : ∀ m, ‖coeff m f‖ ≤ 1) (n k : ℕ) :
    ‖coeff k (f ^ n)‖ ≤ 1 := by
  induction n generalizing k with
  | zero => rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ, coeff_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro x _
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hf _)

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma ex_pow_of_norm_coeff_le_one {u f e : K⟦X⟧} (hu : ‖constantCoeff u‖ < 1)
    (hf : ∀ m, ‖coeff m f‖ ≤ 1) (h : _root_.GlobalTheory.HWL.ExpSub.Ex u f e) (n : ℕ) :
    _root_.GlobalTheory.HWL.ExpSub.Ex u (f ^ n) (e ^ n) := by
  induction n with
  | zero => simpa using ex_one' u
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ex_mul_of_bounded_coeff hu (norm_coeff_pow_le_one_of_norm_coeff_le_one hf n) hf ih h

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma ex_aeval_of_norm_constantCoeff_lt_one {u f e : K⟦X⟧} (hu : ‖constantCoeff u‖ < 1)
    (hf : ∀ m, ‖coeff m f‖ ≤ 1) (he : _root_.GlobalTheory.HWL.ExpSub.Ex u f e) (p : Polynomial K) :
    _root_.GlobalTheory.HWL.ExpSub.Ex u (Polynomial.aeval f p) (Polynomial.aeval e p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add]; exact ex_add_inertia_eigenvalues hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    exact ex_C_mul a (ex_pow_of_norm_coeff_le_one hu hf he n)

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero_of_lt {Y : K⟦X⟧} (h0 : constantCoeff Y = 0) {j d : ℕ} (h : j < d) :
    coeff j (Y ^ d) = 0 := by
  obtain ⟨Y', hY'⟩ := (PowerSeries.X_dvd_iff).mpr h0
  rw [hY', mul_pow, coeff_X_pow_mul', if_neg (by omega)]

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_coeff_subst_mul_pow_le_of_weighted_bound {Y f : K⟦X⟧} (h0 : constantCoeff Y = 0)
    (hY : ∀ m, ‖coeff m Y‖ ≤ 1) {r δ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ)
    (hf : ∀ i, ‖coeff i f‖ * r ^ i ≤ δ) (j : ℕ) :
    ‖coeff j (PowerSeries.subst Y f)‖ * r ^ j ≤ δ := by
  have hs : HasSubst Y := HasSubst.of_constantCoeff_zero' h0
  rw [coeff_subst' hs, finsum_eq_sum_of_support_subset (s := Finset.range (j + 1))]
  · rw [← le_div_iff₀ (by positivity)]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro d hd
    rw [Finset.mem_range] at hd
    rw [smul_eq_mul, norm_mul, le_div_iff₀ (by positivity)]
    calc ‖coeff d f‖ * ‖coeff j (Y ^ d)‖ * r ^ j ≤ ‖coeff d f‖ * 1 * r ^ d :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_coeff_pow_le_one_of_norm_coeff_le_one hY d j) (norm_nonneg _))
            (pow_le_pow_of_le_one hr0.le hr1 (by omega)) (by positivity) (by positivity)
      _ ≤ δ := by rw [mul_one]; exact hf d
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hjd
    exact hd (by rw [coeff_pow_eq_zero_of_constantCoeff_eq_zero_of_lt h0 (by omega), smul_zero])

open PowerSeries Filter Topology in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma ex_subst_of_ex_of_coeff_decay {u v Y a e : K⟦X⟧} (hu : ‖constantCoeff u‖ < 1)
    (h0 : constantCoeff Y = 0) (hY : ∀ m, ‖coeff m Y‖ ≤ 1) (hv : _root_.GlobalTheory.HWL.ExpSub.Ex u Y v)
    (ha : ∀ r : ℝ, 0 < r → r < 1 → Tendsto (fun k : ℕ => ‖coeff k a‖ * r ^ k) atTop (𝓝 0))
    (he : _root_.GlobalTheory.HWL.ExpSub.Ex v a e) : _root_.GlobalTheory.HWL.ExpSub.Ex u (PowerSeries.subst Y a) e := by
  intro k
  have hs : HasSubst Y := HasSubst.of_constantCoeff_zero' h0
  set r : ℝ := max ‖constantCoeff u‖ (1 / 2) with hr
  have hr0 : 0 < r := lt_max_of_lt_right (by norm_num)
  have hr1 : r < 1 := max_lt hu (by norm_num)
  obtain ⟨Cb, hC0, hC⟩ := exists_norm_coeff_aeval_le_mul_of_weighted_bound u (le_max_left _ _) hr0 hr1.le k
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (3 * (Cb + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hCδ : Cb * δ < ε / 3 := by
    rw [hδ, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨Na, hNa⟩ := eventually_atTop.mp ((ha r hr0 hr1).eventually (gt_mem_nhds hδ0))
  obtain ⟨Nb, hNb⟩ := Metric.tendsto_atTop.mp (he k) (ε / 3) (by positivity)
  obtain ⟨Mz, hMz⟩ := Metric.tendsto_atTop.mp
    (ex_aeval_of_norm_constantCoeff_lt_one hu hY hv (trunc (max Na Nb) a) k) (ε / 3) (by positivity)
  refine ⟨Mz, fun m hm => ?_⟩
  have hSP : PowerSeries.subst Y a - Polynomial.aeval Y (trunc (max Na Nb) a) =
      PowerSeries.subst Y (a - (trunc (max Na Nb) a : K⟦X⟧)) := by
    rw [subst_sub hs, subst_coe hs]
  have hdiff : ‖coeff k (Polynomial.aeval u (trunc m (PowerSeries.subst Y a))) -
      coeff k (Polynomial.aeval u (trunc m (Polynomial.aeval Y (trunc (max Na Nb) a))))‖ ≤ Cb * δ := by
    rw [← map_sub, ← map_sub, ← map_sub, hSP]
    apply hC _ _ hδ0.le
    intro j
    rw [coeff_trunc]
    split_ifs
    · apply norm_coeff_subst_mul_pow_le_of_weighted_bound h0 hY hr0 hr1.le hδ0.le
      intro i
      rw [map_sub, Polynomial.coeff_coe, coeff_trunc]
      split_ifs with hi
      · simp [hδ0.le]
      · rw [sub_zero]
        exact (hNa i ((le_max_left Na Nb).trans (not_lt.mp hi))).le
    · simp [hδ0.le]
  have h2 := hNb (max Na Nb) (le_max_right _ _)
  have h3 := hMz m hm
  rw [dist_eq_norm] at h2 h3 ⊢
  set A := coeff k (Polynomial.aeval u (trunc m (PowerSeries.subst Y a)))
  set B := coeff k (Polynomial.aeval u (trunc m (Polynomial.aeval Y (trunc (max Na Nb) a))))
  set W := coeff k (Polynomial.aeval v (trunc (max Na Nb) a))
  calc ‖A - coeff k e‖ ≤ ‖A - B‖ + ‖B - coeff k e‖ := norm_sub_le_norm_sub_add_norm_sub A B _
    _ ≤ ‖A - B‖ + (‖B - W‖ + ‖W - coeff k e‖) := by
        gcongr; exact norm_sub_le_norm_sub_add_norm_sub B W _
    _ < ε := by linarith

open PowerSeries Filter Topology in
open TensorProduct in

theorem _root_.GlobalTheory.HWL.ExpSub.conv_isExp_subst : ∀ (l : ℕ) [Fact l.Prime] (LL : _root_.Formalism.BasicNotions.Loc.FinExt l) (ζ ζ' c : ↥LL.1) (y : PowerSeries ↥(_root_.Formalism.BasicNotions.Loc.OL LL)), ‖((ζ : _root_.Formalism.BasicNotions.Loc.Om l)) - 1‖ < 1 → ‖((ζ' : _root_.Formalism.BasicNotions.Loc.Om l)) - 1‖ < 1 → PowerSeries.constantCoeff y = 0 → _root_.GlobalTheory.HWL.IsExp ζ (PowerSeries.map (algebraMap ↥(_root_.Formalism.BasicNotions.Loc.OL LL) ↥LL.1) y) (PowerSeries.C ζ' * PowerSeries.rescale c (PowerSeries.exp ↥LL.1) - 1) → ∀ a e : PowerSeries ↥LL.1, _root_.GlobalTheory.HWL.Conv a → _root_.GlobalTheory.HWL.IsExp ζ' a e → _root_.GlobalTheory.HWL.Conv (PowerSeries.subst (PowerSeries.map (algebraMap ↥(_root_.Formalism.BasicNotions.Loc.OL LL) ↥LL.1) y) a) ∧ _root_.GlobalTheory.HWL.IsExp ζ (PowerSeries.subst (PowerSeries.map (algebraMap ↥(_root_.Formalism.BasicNotions.Loc.OL LL) ↥LL.1) y) a) (PowerSeries.rescale c e) := by
  intro l _ LL ζ ζ' c y hζ hζ' hy0 hyexp a e ha hae
  have hiff : ∀ (z : ↥LL.1) (f g : PowerSeries ↥LL.1), _root_.GlobalTheory.HWL.IsExp z f g ↔
      _root_.GlobalTheory.HWL.ExpSub.Ex (C z * exp ↥LL.1 - 1) f g := by
    intro z f g
    unfold _root_.GlobalTheory.HWL.IsExp _root_.GlobalTheory.HWL.ExpSub.Ex
    simp only [(Topology.IsInducing.subtypeVal).tendsto_nhds_iff, Function.comp_def]
  set Y := PowerSeries.map (algebraMap ↥(_root_.Formalism.BasicNotions.Loc.OL LL) ↥LL.1) y with hYdef
  have hY : ∀ m, ‖coeff m Y‖ ≤ 1 := by
    intro m
    rw [hYdef, coeff_map]
    exact norm_le_one_of_mem_integralClosure_padicInt _ (coeff m y).2
  have h0 : constantCoeff Y = 0 := by
    rw [hYdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hy0,
      map_zero]
  have hu : ‖constantCoeff (C ζ * exp ↥LL.1 - 1)‖ < 1 := by
    have h : constantCoeff (C ζ * exp ↥LL.1 - 1) = ζ - 1 := by simp
    rw [h]
    show ‖((ζ - 1 : ↥LL.1) : _root_.Formalism.BasicNotions.Loc.Om l)‖ < 1
    push_cast
    exact hζ
  have hv := (hiff ζ Y _).mp hyexp
  have hresc : rescale c (C ζ' * exp ↥LL.1 - 1) = C ζ' * rescale c (exp ↥LL.1) - 1 := by
    rw [map_sub, map_mul, map_one, rescale_C_eq_C]
  have he := ex_rescale c ((hiff ζ' a e).mp hae)
  rw [hresc] at he
  refine ⟨?_, (hiff ζ _ _).mpr (ex_subst_of_ex_of_coeff_decay hu h0 hY hv ha he)⟩
  intro r hr0 hr1
  set s : ℝ := (r + 1) / 2 with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s < 1 := by linarith
  have hrs : r < s := by linarith
  obtain ⟨B, hB⟩ := (ha s hs0 hs1).bddAbove_range
  have hB' : ∀ i, ‖coeff i a‖ * s ^ i ≤ B := fun i => hB ⟨i, rfl⟩
  have hB0 : 0 ≤ B := (by positivity : (0 : ℝ) ≤ ‖coeff 0 a‖ * s ^ 0).trans (hB' 0)
  have hS : ∀ k, ‖coeff k (PowerSeries.subst Y a)‖ * s ^ k ≤ B :=
    norm_coeff_subst_mul_pow_le_of_weighted_bound h0 hY hs0 hs1.le hB0 hB'
  have hq : Tendsto (fun k : ℕ => B * (r / s) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((div_lt_one hs0).mpr hrs)).const_mul B
  refine squeeze_zero (fun k => by positivity) (fun k => ?_) hq
  calc ‖coeff k (PowerSeries.subst Y a)‖ * r ^ k =
        ‖coeff k (PowerSeries.subst Y a)‖ * s ^ k * (r / s) ^ k := by
          rw [mul_assoc, ← mul_pow]
          congr 2
          field_simp
    _ ≤ B * (r / s) ^ k := by gcongr; exact hS k

end GlobalTheory.HWL.ExpSub
