import Mathlib
import GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes

namespace GroundTheory.Global

open NumberField IsDedekindDomain Filter Topology Set Ideal

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def dedekindZetaTerm (s : ℝ) (n : ℕ) : ℝ :=
  (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)

def dedekindZetaReal (s : ℝ) : ℝ :=
  ∑' n, dedekindZetaTerm K s n

theorem dedekindZetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ dedekindZetaTerm K s n := by
  unfold dedekindZetaTerm
  positivity

theorem dedekindZeta_ofReal {s : ℝ} (hs : s ≠ 0) :
    dedekindZeta K s = (dedekindZetaReal K s : ℂ) := by
  rw [dedekindZeta, LSeries, dedekindZetaReal, Complex.ofReal_tsum]
  congr 1
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dedekindZetaTerm, Real.zero_rpow (neg_ne_zero.mpr hs)]
  · rw [LSeries.term_of_ne_zero hn, dedekindZetaTerm, Complex.ofReal_mul,
      Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.cpow_neg,
      div_eq_mul_inv]
    simp

theorem tendsto_sub_one_mul_dedekindZetaReal :
    Tendsto (fun s : ℝ => (s - 1) * dedekindZetaReal K s) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  rw [Complex.ofReal_re] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
  have hs0 : s ≠ 0 := by simp only [mem_Ioi] at hs; linarith
  simp only [Function.comp_apply]
  rw [dedekindZeta_ofReal K hs0, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem finite_absNorm_lt (N : ℕ) : {I : Ideal (𝓞 K) | absNorm I < N}.Finite := by
  have : {I : Ideal (𝓞 K) | absNorm I < N} = ⋃ n ∈ Set.Iio N, {I | absNorm I = n} := by
    ext I
    simp
  rw [this]
  exact (Set.finite_Iio N).biUnion fun n _ => Ideal.finite_setOfPred_absNorm_eq n

theorem sum_range_dedekindZetaTerm (s : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, dedekindZetaTerm K s n =
      ∑ I ∈ (finite_absNorm_lt K N).toFinset, (absNorm I : ℝ) ^ (-s) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun I : Ideal (𝓞 K) => absNorm I)
    (t := Finset.range N) (fun I hI => by simpa using hI)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_congr rfl (fun I hI => by rw [(Finset.mem_filter.mp hI).2]),
    Finset.sum_const, nsmul_eq_mul, dedekindZetaTerm]
  congr 2
  have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  have : ((finite_absNorm_lt K N).toFinset.filter fun I => absNorm I = n) = hfin.toFinset := by
    ext I
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ Finset.mem_range.mp hn, h⟩
  rw [this, ← Nat.card_eq_card_finite_toFinset]
  rfl

theorem geom_sum_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (M : ℕ) :
    ∑ k ∈ Finset.range M, x ^ k ≤ Real.exp (x + 2 * x ^ 2) := by
  have h1 : ∑ k ∈ Finset.range M, x ^ k ≤ 1 / (1 - x) := by
    rw [Finset.range_eq_Ico]
    calc ∑ k ∈ Finset.Ico 0 M, x ^ k ≤ x ^ 0 / (1 - x) :=
          geom_sum_Ico_le_of_lt_one hx0 (by linarith)
      _ = 1 / (1 - x) := by rw [pow_zero]
  have h2 : 1 / (1 - x) ≤ 1 + x + 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
  have h3 := Real.add_one_le_exp (x + 2 * x ^ 2)
  linarith

theorem exp_sub_sq_le_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (x - x ^ 2) ≤ 1 + x := by
  have hy0 : 0 ≤ x - x ^ 2 := by nlinarith
  have hy1 : x - x ^ 2 ≤ x := by nlinarith
  have h := Real.abs_exp_sub_one_sub_id_le (x := x - x ^ 2) (by rw [abs_le]; constructor <;> linarith)
  have h' := (abs_le.mp h).2
  nlinarith [mul_le_mul hy1 hy1 hy0 hx0]

variable {K}

theorem two_le_absNorm_of_prime {p : Ideal (𝓞 K)} (hp : Prime p) : 2 ≤ absNorm p := by
  have h0 : absNorm p ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hp.ne_zero
  have h1 : absNorm p ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact (Ideal.isPrime_of_prime hp).ne_top
  omega

theorem rpow_neg_absNorm_le_half {p : Ideal (𝓞 K)} (hp : Prime p) {s : ℝ} (hs : 1 ≤ s) :
    (absNorm p : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ absNorm p := by exact_mod_cast two_le_absNorm_of_prime hp
  calc (absNorm p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

def heightOneOfPrime {p : Ideal (𝓞 K)} (hp : Prime p) : HeightOneSpectrum (𝓞 K) :=
  ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩

theorem absNorm_eq_prod_count {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (P : Finset (Ideal (𝓞 K)))
    (hP : (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆ P) :
    absNorm I = ∏ p ∈ P, absNorm p ^ (UniqueFactorizationMonoid.normalizedFactors I).count p := by
  classical
  have hprod : (UniqueFactorizationMonoid.normalizedFactors I).prod = I :=
    associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hI)
  conv_lhs => rw [← hprod]
  rw [map_multiset_prod, Finset.prod_multiset_map_count]
  refine Finset.prod_subset hP fun p _ hp => ?_
  rw [Multiset.count_eq_zero.mpr (fun h => hp (Multiset.mem_toFinset.mpr h)), pow_zero]

theorem sum_rpow_neg_le_exp_tsum (T : Finset (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) ≤
      Real.exp (∑' w : HeightOneSpectrum (𝓞 K),
        ((absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2)) := by
  classical
  set x : Ideal (𝓞 K) → ℝ := fun p => (absNorm p : ℝ) ^ (-s) with hxdef
  have hx0 : ∀ p, 0 ≤ x p := fun p => by positivity
  have hs0 : -s ≠ 0 := by intro h; linarith
  have hbot : x ⊥ = 0 := by simp [x, Real.zero_rpow hs0]
  set nf := fun I : Ideal (𝓞 K) => UniqueFactorizationMonoid.normalizedFactors I with hnf
  set T' := T.erase ⊥ with hT'
  set P : Finset (Ideal (𝓞 K)) := T'.biUnion fun I => (nf I).toFinset with hP
  set M : ℕ := T'.sup (fun I => Multiset.card (nf I)) + 1 with hM
  have hPprime : ∀ p ∈ P, Prime p := by
    intro p hp
    obtain ⟨I, _, hpI⟩ := Finset.mem_biUnion.mp hp
    exact UniqueFactorizationMonoid.prime_of_normalized_factor p (Multiset.mem_toFinset.mp hpI)
  have hxI : ∀ I ∈ T', x I = ∏ p : P, x p.1 ^ (nf I).count p.1 := by
    intro I hI
    have hI0 : I ≠ ⊥ := (Finset.mem_erase.mp hI).1
    rw [Finset.prod_coe_sort P (fun p => x p ^ (nf I).count p)]
    simp only [x]
    rw [absNorm_eq_prod_count hI0 P (Finset.subset_biUnion_of_mem (fun I => (nf I).toFinset) hI),
      Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  let E : Ideal (𝓞 K) → (P → ℕ) := fun I p => (nf I).count p.1
  have hE : Set.InjOn E T' := by
    intro I hI J hJ hIJ
    have hI0 : I ≠ ⊥ := (Finset.mem_erase.mp hI).1
    have hJ0 : J ≠ ⊥ := (Finset.mem_erase.mp hJ).1
    have hnfeq : nf I = nf J := by
      ext q
      by_cases hq : q ∈ P
      · exact congrFun hIJ ⟨q, hq⟩
      · have hqI : q ∉ nf I := fun h =>
          hq (Finset.mem_biUnion.mpr ⟨I, hI, Multiset.mem_toFinset.mpr h⟩)
        have hqJ : q ∉ nf J := fun h =>
          hq (Finset.mem_biUnion.mpr ⟨J, hJ, Multiset.mem_toFinset.mpr h⟩)
        rw [Multiset.count_eq_zero.mpr hqI, Multiset.count_eq_zero.mpr hqJ]
    rw [← associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hI0),
      ← associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hJ0)]
    exact congrArg Multiset.prod hnfeq
  have hEM : ∀ I ∈ T', E I ∈ Fintype.piFinset (fun _ : P => Finset.range M) := by
    intro I hI
    refine Fintype.mem_piFinset.mpr fun p => Finset.mem_range.mpr ?_
    exact Nat.lt_succ_of_le ((Multiset.count_le_card _ _).trans
      (Finset.le_sup (f := fun I => Multiset.card (nf I)) hI))
  have hxhalf : ∀ p : P, x p.1 ≤ 1 / 2 := fun p =>
    rpow_neg_absNorm_le_half (hPprime p.1 p.2) hs.le
  let ι : P → HeightOneSpectrum (𝓞 K) := fun p => heightOneOfPrime (hPprime p.1 p.2)
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)
  have hsum : Summable fun w : HeightOneSpectrum (𝓞 K) =>
      (absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2 := by
    have h1 := summable_absNorm_rpow_neg (L := K) hs
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun w => ?_) (h1.mul_left 3)
    have hw0 : (0 : ℝ) ≤ (absNorm w.asIdeal : ℝ) ^ (-s) := by positivity
    have hw1 := rpow_neg_absNorm_le_half w.prime hs.le
    nlinarith
  calc ∑ I ∈ T, x I = ∑ I ∈ T', x I := (Finset.sum_erase (f := x) T hbot).symm
    _ = ∑ I ∈ T', ∏ p : P, x p.1 ^ E I p := Finset.sum_congr rfl hxI
    _ = ∑ e ∈ T'.image E, ∏ p : P, x p.1 ^ e p :=
        (Finset.sum_image (f := fun e : P → ℕ => ∏ p : P, x p.1 ^ e p) hE).symm
    _ ≤ ∑ e ∈ Fintype.piFinset (fun _ : P => Finset.range M), ∏ p : P, x p.1 ^ e p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun e he => ?_)
          (fun _ _ _ => Finset.prod_nonneg fun _ _ => pow_nonneg (hx0 _) _)
        obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp he
        exact hEM I hI
    _ = ∏ p : P, ∑ k ∈ Finset.range M, x p.1 ^ k :=
        (Finset.prod_univ_sum (fun _ : P => Finset.range M) (fun p k => x p.1 ^ k)).symm
    _ ≤ ∏ p : P, Real.exp (x p.1 + 2 * x p.1 ^ 2) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg (hx0 _) _)
          (fun p _ => geom_sum_le_exp (hx0 _) (hxhalf p) M)
    _ = Real.exp (∑ p : P, (x p.1 + 2 * x p.1 ^ 2)) :=
        (Real.exp_sum Finset.univ fun p : P => x p.1 + 2 * x p.1 ^ 2).symm
    _ ≤ _ := by
        refine Real.exp_le_exp.mpr ?_
        calc ∑ p : P, (x p.1 + 2 * x p.1 ^ 2)
            = ∑ w ∈ Finset.univ.image ι, ((absNorm w.asIdeal : ℝ) ^ (-s) +
                2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2) :=
              (Finset.sum_image (f := fun w : HeightOneSpectrum (𝓞 K) =>
                (absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2)
                (s := Finset.univ) (g := ι) (fun a _ b _ h => hι h)).symm
          _ ≤ _ := hsum.sum_le_tsum _ (fun _ _ => by positivity)

theorem prod_one_add_rpow_neg_eq_sum (P : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    ∏ w ∈ P, (1 + (absNorm w.asIdeal : ℝ) ^ (-s)) =
      ∑ I ∈ P.powerset.image (fun A => ∏ w ∈ A, w.asIdeal), (absNorm I : ℝ) ^ (-s) := by
  classical
  have hinj : Set.InjOn (fun A : Finset (HeightOneSpectrum (𝓞 K)) => ∏ w ∈ A, w.asIdeal)
      P.powerset := by
    have key : ∀ A B : Finset (HeightOneSpectrum (𝓞 K)),
        ∏ w ∈ A, w.asIdeal = ∏ w ∈ B, w.asIdeal → A ⊆ B := by
      intro A B hAB w hw
      have hle : ∏ w ∈ B, w.asIdeal ≤ w.asIdeal := by
        rw [← hAB]
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hw)
      obtain ⟨w', hw', hle'⟩ := (Ideal.IsPrime.prod_le w.isPrime).mp hle
      have : w' = w := HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle')
      exact this ▸ hw'
    intro A _ B _ hAB
    exact le_antisymm (key A B hAB) (key B A hAB.symm)
  rw [Finset.prod_one_add, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [map_prod, Nat.cast_prod, Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]

theorem sum_rpow_neg_le_dedekindZetaReal (T : Finset (Ideal (𝓞 K))) {s : ℝ}
    (hζ : Summable (dedekindZetaTerm K s)) :
    ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) ≤ dedekindZetaReal K s := by
  classical
  set N := T.sup (fun I => absNorm I) + 1
  have hsub : T ⊆ (finite_absNorm_lt K N).toFinset := by
    intro I hI
    rw [Set.Finite.mem_toFinset, mem_ofPred_eq]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun I => absNorm I) hI)
  calc ∑ I ∈ T, (absNorm I : ℝ) ^ (-s)
      ≤ ∑ I ∈ (finite_absNorm_lt K N).toFinset, (absNorm I : ℝ) ^ (-s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ n ∈ Finset.range N, dedekindZetaTerm K s n := (sum_range_dedekindZetaTerm K s N).symm
    _ ≤ dedekindZetaReal K s :=
        hζ.sum_le_tsum _ (fun n _ => dedekindZetaTerm_nonneg K s n)

theorem one_le_dedekindZetaReal {s : ℝ} (hζ : Summable (dedekindZetaTerm K s)) :
    1 ≤ dedekindZetaReal K s := by
  have := sum_rpow_neg_le_dedekindZetaReal {(⊤ : Ideal (𝓞 K))} hζ
  simpa using this

theorem dedekindZetaReal_le_exp {s : ℝ} (hs : 1 < s) :
    dedekindZetaReal K s ≤
      Real.exp (∑' w : HeightOneSpectrum (𝓞 K),
        ((absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2)) := by
  refine Real.tsum_le_of_sum_range_le (fun n => dedekindZetaTerm_nonneg K s n) fun N => ?_
  rw [sum_range_dedekindZetaTerm]
  exact sum_rpow_neg_le_exp_tsum _ hs

theorem abs_log_dedekindZetaReal_sub_tsum_le {s : ℝ} (hs : 1 < s)
    (hζ : Summable (dedekindZetaTerm K s)) :
    |Real.log (dedekindZetaReal K s) -
        ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-s)| ≤
      2 * ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
  set x := fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s) with hx
  set y := fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-(2 : ℝ)) with hy
  have hxs : Summable x := summable_absNorm_rpow_neg hs
  have hys : Summable y := summable_absNorm_rpow_neg (by norm_num)
  have hx0 : ∀ w, 0 ≤ x w := fun w => by positivity
  have hxy : ∀ w, x w ^ 2 ≤ y w := by
    intro w
    have h1 : (1 : ℝ) ≤ absNorm w.asIdeal := by exact_mod_cast one_le_absNorm w
    simp only [x, y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)
  have hx2s : Summable fun w => x w ^ 2 :=
    Summable.of_nonneg_of_le (fun w => by positivity) hxy hys
  have hQ : ∑' w, x w ^ 2 ≤ ∑' w, y w := Summable.tsum_le_tsum hxy hx2s hys
  have hQ0 : 0 ≤ ∑' w, x w ^ 2 := tsum_nonneg fun w => by positivity
  have hζpos : 0 < dedekindZetaReal K s := lt_of_lt_of_le one_pos (one_le_dedekindZetaReal hζ)
  have hup : Real.log (dedekindZetaReal K s) ≤ ∑' w, x w + 2 * ∑' w, x w ^ 2 := by
    rw [Real.log_le_iff_le_exp hζpos]
    have := dedekindZetaReal_le_exp (K := K) hs
    rwa [Summable.tsum_add hxs (hx2s.mul_left 2), tsum_mul_left] at this
  have hlow : ∑' w, x w - ∑' w, x w ^ 2 ≤ Real.log (dedekindZetaReal K s) := by
    rw [← Summable.tsum_sub hxs hx2s]
    refine (hxs.sub hx2s).tsum_le_of_sum_le fun F => ?_
    rw [Real.le_log_iff_exp_le hζpos, Real.exp_sum]
    calc ∏ w ∈ F, Real.exp (x w - x w ^ 2) ≤ ∏ w ∈ F, (1 + x w) :=
          Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
            (fun w _ => exp_sub_sq_le_one_add (hx0 w) (rpow_neg_absNorm_le_half w.prime hs.le))
      _ = _ := prod_one_add_rpow_neg_eq_sum F s
      _ ≤ _ := sum_rpow_neg_le_dedekindZetaReal _ hζ
  rw [abs_le]
  constructor <;> linarith

variable (K) in

theorem eventually_summable_dedekindZetaTerm :
    ∀ᶠ s in 𝓝[>] (1 : ℝ), Summable (dedekindZetaTerm K s) := by
  have h := (tendsto_sub_one_mul_dedekindZetaReal K).eventually
    (lt_mem_nhds (dedekindZeta_residue_pos K))
  filter_upwards [h] with s hs
  by_contra hns
  rw [dedekindZetaReal, tsum_eq_zero_of_not_summable hns, mul_zero] at hs
  exact lt_irrefl _ hs

theorem primeIdealZetaSum_univ (s : ℝ) :
    (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
      ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-s) := by
  rw [Set.primeIdealZetaSum_def]
  exact tsum_univ (f := fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s))

variable (K) in

theorem exists_abs_primeIdealZetaSum_add_log_le :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      |(univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s + Real.log (s - 1)| ≤ C := by
  set R := dedekindZeta_residue K
  set Y := ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-(2 : ℝ))
  have hlog : Tendsto (fun s : ℝ => Real.log ((s - 1) * dedekindZetaReal K s)) (𝓝[>] 1)
      (𝓝 (Real.log R)) :=
    (tendsto_sub_one_mul_dedekindZetaReal K).log (dedekindZeta_residue_ne_zero K)
  have hnear : ∀ᶠ s in 𝓝[>] (1 : ℝ),
      |Real.log ((s - 1) * dedekindZetaReal K s) - Real.log R| ≤ 1 := by
    filter_upwards [Metric.tendsto_nhds.mp hlog 1 one_pos] with s hs
    rw [Real.dist_eq] at hs
    exact hs.le
  refine ⟨2 * Y + |Real.log R| + 1, ?_⟩
  filter_upwards [hnear, eventually_summable_dedekindZetaTerm K, self_mem_nhdsWithin]
    with s hs hζ hs1
  have hs1' : 1 < s := hs1
  have hζpos : 0 < dedekindZetaReal K s :=
    lt_of_lt_of_le one_pos (one_le_dedekindZetaReal hζ)
  have hsplit : Real.log ((s - 1) * dedekindZetaReal K s) =
      Real.log (s - 1) + Real.log (dedekindZetaReal K s) :=
    Real.log_mul (by linarith) hζpos.ne'
  have hcmp := abs_log_dedekindZetaReal_sub_tsum_le (K := K) hs1' hζ
  rw [hsplit] at hs
  rw [primeIdealZetaSum_univ]
  rw [abs_le] at hs hcmp ⊢
  have h1 := le_abs_self (Real.log R)
  have h2 := neg_abs_le (Real.log R)
  constructor <;> linarith [hs.1, hs.2, hcmp.1, hcmp.2]

variable (K) in

theorem tendsto_primeIdealZetaSum_univ_atTop :
    Tendsto (fun s => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)
      (𝓝[>] 1) atTop := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_add_log_le K
  have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨?_, eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => show 0 < s - 1 by linarith⟩
    have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 0) := by
      simpa using (continuous_sub_right (1 : ℝ)).tendsto 1
    exact this.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun s : ℝ => -Real.log (s - 1) + -C) (𝓝[>] 1) atTop :=
    tendsto_atTop_add_const_right _ (-C)
      (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1))
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [hC] with s hs
  have := (abs_le.mp hs).1
  linarith

end

end GroundTheory.Global
