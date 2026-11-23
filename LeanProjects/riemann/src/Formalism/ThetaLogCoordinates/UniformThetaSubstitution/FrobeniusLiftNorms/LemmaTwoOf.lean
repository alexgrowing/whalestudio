import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace LemTwo

section Slice

variable {K : Type} [Field K]

def sl (G : MvPowerSeries (Fin 2) K) (m : ℕ) : PowerSeries K :=
  PowerSeries.mk fun i => MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) G

def ext3 (e : Fin 2 →₀ ℕ) (m : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.embDomain Fin.castSuccEmb e + Finsupp.single 2 m

theorem include_three_eq_rename (g : MvPowerSeries (Fin 2) K) :
    in3 g = MvPowerSeries.rename (Fin.castSuccEmb (n := 2)) g := by
  rw [MvPowerSeries.rename_eq_subst, in3]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem embDomain_two (e : Fin 2 →₀ ℕ) : Finsupp.embDomain Fin.castSuccEmb e (2 : Fin 3) = 0 := by
  rw [Finsupp.embDomain_notin_range]
  rintro ⟨i, hi⟩
  have h1 := congrArg Fin.val hi
  have h2 := i.isLt
  simp at h1
  omega

private theorem coeff_rename_map_lemma {σ τ : Type} (f : σ → τ) [Filter.TendstoCofinite f]
    (hf : Function.Injective f) (g : MvPowerSeries σ K) (u : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.mapDomain f u) (MvPowerSeries.rename f g) = MvPowerSeries.coeff u g := by
  classical
  rw [MvPowerSeries.coeff_rename, Finset.sum_eq_single_of_mem u]
  · simp
  · intro b hb hne
    exfalso
    apply hne
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hb
    exact Finsupp.mapDomain_injective hf hb

theorem coeff_include_three_mul (g : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m j : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (in3 g * MvPowerSeries.X 2 ^ j) =
      if j = m then MvPowerSeries.coeff e g else 0 := by
  classical
  rw [include_three_eq_rename]
  by_cases h : j = m
  · subst h
    rw [if_pos rfl, MvPowerSeries.X_pow_eq, ext3, MvPowerSeries.coeff_add_mul_monomial, mul_one,
      Finsupp.embDomain_eq_mapDomain]
    exact coeff_rename_map_lemma _ (Fin.castSuccEmb (n := 2)).injective g e
  · rw [if_neg h, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    replace hab : a + b = ext3 e m := by simpa using hab
    rw [MvPowerSeries.coeff_X_pow]
    split_ifs with hb
    · rw [mul_one]
      apply MvPowerSeries.coeff_rename_eq_zero
      rintro ⟨u, hu⟩
      simp only at hb hu
      have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) hab
      simp only [Finsupp.add_apply, hb, ext3] at h2
      rw [← hu, Finsupp.mapDomain_notin_range, embDomain_two] at h2
      · simp at h2
        omega
      · rintro ⟨i, hi⟩
        have h1 := congrArg Fin.val hi
        have h3 := i.isLt
        simp at h1
        omega
    · rw [mul_zero]

theorem constantCoeff_law_first_two_of_three {g : MvPowerSeries (Fin 2) K} (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (in3 g) = 0 := by
  rw [include_three_eq_rename, MvPowerSeries.constantCoeff_rename, hg]

theorem include_three_pow (g : MvPowerSeries (Fin 2) K) (k : ℕ) : in3 g ^ k = in3 (g ^ k) := by
  rw [include_three_eq_rename, include_three_eq_rename, map_pow]

theorem include_three_X (i : Fin 2) :
    in3 (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = MvPowerSeries.X (Fin.castSucc i) := by
  rw [include_three_eq_rename, MvPowerSeries.rename_X]
  rfl

theorem fin_two_vector_eq_matrixVecCons (d : Fin 2 →₀ ℕ) : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext i
  fin_cases i <;> simp

theorem coeff_pow_high {ι : Type} {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0)
    {e : ι →₀ ℕ} {k : ℕ} (hk : e.degree < k) : MvPowerSeries.coeff e (f ^ k) = 0 :=
  MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hk)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf))

theorem coeff_subst_slice {f : MvPowerSeries (Fin 2) K} (hf : MvPowerSeries.constantCoeff f = 0)
    (G : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (MvPowerSeries.subst ![in3 f, MvPowerSeries.X 2] G) =
      MvPowerSeries.coeff e (PowerSeries.subst f (sl G m)) := by
  classical
  have ha : MvPowerSeries.HasSubst ![in3 f, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      fin_cases s
      · exact constantCoeff_law_first_two_of_three hf
      · simp)
  have hb : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  rw [MvPowerSeries.coeff_subst ha, PowerSeries.coeff_subst hb]
  have hterm : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff (ext3 e m)
      (d.prod fun s k => (![in3 f, MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) K) s ^ k) =
        if d 1 = m then MvPowerSeries.coeff e (f ^ d 0) else 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [include_three_pow, coeff_include_three_mul]
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset _
      (s := (Finset.range (e.degree + 1)).image (fun i => Finsupp.single (0 : Fin 2) i + Finsupp.single 1 m)),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (e.degree + 1))]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      simp [sl]
    · intro x _ y _ hxy
      have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hxy
      simpa using this
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hi (by rw [coeff_pow_high hf (by omega), smul_zero])
  · intro d hd
    rw [Function.mem_support] at hd
    split_ifs at hd with h1
    · simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      refine ⟨d 0, ?_, ?_⟩
      · by_contra hc
        exact hd (by rw [coeff_pow_high hf (by omega), smul_zero])
      · rw [← h1]
        exact (fin_two_vector_eq_matrixVecCons d).symm
    · exact absurd (smul_zero _) hd

theorem coeff_partial_coboundary {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (G : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (d1 F G) = MvPowerSeries.coeff e (cob F (sl G m)) := by
  have h0 := coeff_subst_slice (f := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
    (MvPowerSeries.constantCoeff_X 0) G e m
  have h1 := coeff_subst_slice (f := (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K))
    (MvPowerSeries.constantCoeff_X 1) G e m
  rw [include_three_X] at h0 h1
  rw [d1, map_sub, map_sub, coeff_subst_slice hF, cob, map_sub, map_sub, at1, at1]
  rw [← h0, ← h1]
  rfl

end Slice

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_mul {ι : Type} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun q _ => by rw [norm_mul]; exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _))

end Norm

section Top

variable {K : Type} [Field K]

end Top

section Additive

variable {K : Type} [Field K]

theorem cob_add {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f + g) = cob F f + cob F g := by
  unfold cob at1
  rw [PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    PowerSeries.subst_add (PowerSeries.HasSubst.X 0), PowerSeries.subst_add (PowerSeries.HasSubst.X 1)]
  ring

theorem coeff_one_lgF {p : ℕ} (hp : 2 ≤ p) : PowerSeries.coeff 1 (lgF K p) = 1 := by
  rw [lgF, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_range_one]
  have h4 : 4 ≤ p ^ 2 := by nlinarith
  have hne : (1 : ℕ) ≠ (p ^ 2) ^ 1 := by rw [pow_one]; omega
  rw [if_neg hne, if_pos (by rw [pow_zero]), pow_zero, inv_one, add_zero]

theorem swap_two_eq_rename (H : MvPowerSeries (Fin 2) K) :
    swap2 H = MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1).toEmbedding H := by
  rw [MvPowerSeries.rename_eq_subst, swap2]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem coeff_swap2 (H : MvPowerSeries (Fin 2) K) (i k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) (swap2 H) =
      MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 i) H := by
  rw [swap_two_eq_rename]
  have hu : Finsupp.mapDomain (⇑(Equiv.swap (0 : Fin 2) 1).toEmbedding)
      (Finsupp.single 0 k + Finsupp.single 1 i) = Finsupp.single 0 i + Finsupp.single 1 k := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact add_comm _ _
  rw [← hu, coeff_rename_map_lemma _ (Equiv.swap (0 : Fin 2) 1).toEmbedding.injective]

def asm (R : ℕ → PowerSeries K) : MvPowerSeries (Fin 2) K :=
  fun n => PowerSeries.coeff (n 0) (R (n 1))

theorem pow_parity {p : ℕ} (hp : 2 ≤ p) (i j : ℕ) : p * (p ^ 2) ^ i ≠ (p ^ 2) ^ j := by
  intro h
  have e1 : p * (p ^ 2) ^ i = p ^ (2 * i + 1) := by ring
  have e2 : (p ^ 2) ^ j = p ^ (2 * j) := by ring
  rw [e1, e2] at h
  have := Nat.pow_right_injective hp h
  omega

theorem coeff_lgF_odd {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    PowerSeries.coeff (p * (p ^ 2) ^ i) (lgF K p) = 0 := by
  rw [lgF, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (pow_parity hp i j)]

theorem coeff_g0F_even {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ i) (g0F K p) = 0 := by
  rw [g0F, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (fun h => pow_parity hp j i h.symm)]

end Additive

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_one {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max x (-y)).trans (max_le hx (by rwa [norm_neg]))

theorem eq_zero_of_div {p : ℕ} (hp : 2 ≤ p) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {x : K}
    (h : ∀ N : ℕ, ∃ i, N ≤ i ∧ ‖((p : K) ^ i)⁻¹ * x‖ ≤ 1) : x = 0 := by
  by_contra hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hp1 : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hxpos hp1
  obtain ⟨i, hi, hle⟩ := h N
  have hpos : (0 : ℝ) < (p : ℝ) ^ i := by positivity
  rw [norm_mul, norm_inv, norm_pow, hnp, inv_pow, inv_inv] at hle
  have h1 : ‖x‖ ≤ ((p : ℝ)⁻¹) ^ i := by
    rw [inv_pow]
    calc ‖x‖ = ((p : ℝ) ^ i)⁻¹ * ((p : ℝ) ^ i * ‖x‖) := by field_simp
      _ ≤ ((p : ℝ) ^ i)⁻¹ * 1 := by gcongr
      _ = ((p : ℝ) ^ i)⁻¹ := mul_one _
  have h2 : ((p : ℝ)⁻¹) ^ i ≤ ((p : ℝ)⁻¹) ^ N := pow_le_pow_of_le_one (by positivity) hp1.le hi
  linarith

end Norm

end LemTwo

open LemTwo in

theorem LemmaTwo_of (h1 : LemmaOne) (hL : LawSymm) : LemmaTwo := by
  intro K _ _ _ _ p σ hU F hF H hH hd hd'
  obtain ⟨hp, -, hnp, -, -⟩ := id hU
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨hF0, -, -⟩ := id hF
  have np : ∀ k : ℕ, ‖((p : K) ^ k)⁻¹‖ = (p : ℝ) ^ k := by
    intro k
    rw [norm_inv, norm_pow, hnp, inv_pow, inv_inv]
  have zero_of_bdd : ∀ (c : K) (M : ℝ), (∀ N : ℕ, ∃ k, N ≤ k ∧ ‖c * ((p : K) ^ k)⁻¹‖ ≤ M) → c = 0 := by
    intro c M h
    by_contra hc
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖c‖) hp1
    obtain ⟨k, hk, hle⟩ := h n
    rw [norm_mul, np] at hle
    have hpk : (p : ℝ) ^ n ≤ (p : ℝ) ^ k := pow_le_pow_right₀ hp1.le hk
    have h3 : M / ‖c‖ < (p : ℝ) ^ k := lt_of_lt_of_le hn hpk
    rw [div_lt_iff₀ hcpos] at h3
    linarith [mul_comm ‖c‖ ((p : ℝ) ^ k)]
  have ultra : ∀ {a b : K} {M : ℝ}, ‖a - b‖ ≤ 1 → ‖b‖ ≤ M → 1 ≤ M → ‖a‖ ≤ M := by
    intro a b M h hb hM
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ max ‖a - b‖ ‖b‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ M := max_le (h.trans hM) hb
  have hpp : 2 ≤ p ^ 2 := by nlinarith
  have lg_pow : ∀ k : ℕ, PowerSeries.coeff ((p ^ 2) ^ k) (lgF K p) = ((p : K) ^ k)⁻¹ := by
    intro k
    rw [lgF, PowerSeries.coeff_mk, Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Nat.pow_right_injective hpp h).symm
    · intro hk
      exfalso
      apply hk
      rw [Finset.mem_range]
      have : k < (p ^ 2) ^ k := Nat.lt_pow_self (by omega)
      omega
  have g0_pow : ∀ k : ℕ, PowerSeries.coeff (p * (p ^ 2) ^ k) (g0F K p) = ((p : K) ^ (k + 1))⁻¹ := by
    intro k
    rw [g0F, PowerSeries.coeff_mk, Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Nat.pow_right_injective hpp (Nat.eq_of_mul_eq_mul_left (by omega) h)).symm
    · intro hk
      exfalso
      apply hk
      rw [Finset.mem_range]
      have : k < (p ^ 2) ^ k := Nat.lt_pow_self (by omega)
      have : (p ^ 2) ^ k ≤ p * (p ^ 2) ^ k := Nat.le_mul_of_pos_left _ (by omega)
      omega
  have lg_zero : ∀ m : ℕ, (∀ l, m ≠ (p ^ 2) ^ l) → PowerSeries.coeff m (lgF K p) = 0 := by
    intro m hm
    rw [lgF, PowerSeries.coeff_mk]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (hm j)]
  have g01 : PowerSeries.coeff 1 (g0F K p) = 0 := by
    have := LemTwo.coeff_g0F_even (K := K) hp2 0
    rwa [pow_zero] at this
  have lg1 : PowerSeries.coeff 1 (lgF K p) = 1 := LemTwo.coeff_one_lgF hp2
  have hH2 : DivAB (swap2 H) := by
    intro n hn
    rw [LemTwo.fin_two_vector_eq_matrixVecCons n, LemTwo.coeff_swap2]
    apply hH
    rcases hn with h | h
    · right
      simp [h]
    · left
      simp [h]
  have cobInt : ∀ G : MvPowerSeries (Fin 2) K, Integral (d1 F G) → ∀ m, Integral (cob F (sl G m)) := by
    intro G hG m e
    rw [← LemTwo.coeff_partial_coboundary hF0 G e m]
    exact hG _
  have c0 : ∀ G : MvPowerSeries (Fin 2) K, DivAB G → ∀ m, PowerSeries.constantCoeff (sl G m) = 0 := by
    intro G hG m
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sl, PowerSeries.coeff_mk]
    apply hG
    left
    simp
  choose α β R hα hR hsl using fun m => h1 K p σ hU F hF (sl H m) (c0 H hH m) (cobInt H hd m)
  choose α' β' R' hα' hR' hsl' using fun m =>
    h1 K p σ hU F hF (sl (swap2 H) m) (c0 _ hH2 m) (cobInt _ hd' m)
  have cH : ∀ i m, MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) H =
      α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p) +
        PowerSeries.coeff i (R m) := by
    intro i m
    have h3 := congrArg (PowerSeries.coeff i) (hsl m)
    rw [sl, PowerSeries.coeff_mk] at h3
    rw [h3, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  have cH' : ∀ i m, MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) H =
      α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p) +
        PowerSeries.coeff m (R' i) := by
    intro i m
    have h3 := congrArg (PowerSeries.coeff m) (hsl' i)
    rw [sl, PowerSeries.coeff_mk, LemTwo.coeff_swap2] at h3
    rw [h3, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  have star : ∀ i m, ‖(α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p)) -
      (α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p))‖ ≤ 1 := by
    intro i m
    have e : (α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p)) -
        (α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p)) =
        PowerSeries.coeff m (R' i) - PowerSeries.coeff i (R m) := by
      have e1 := cH i m
      have e2 := cH' i m
      linear_combination e2 - e1
    rw [e]
    exact LemTwo.norm_sub_le_one (hR' i m) (hR m i)
  have hA : ∀ k, β' (p * (p ^ 2) ^ k) = 0 := by
    intro k
    apply zero_of_bdd _ ((p : ℝ) ^ (k + 1))
    intro N
    refine ⟨N, le_rfl, ?_⟩
    have s := star (p * (p ^ 2) ^ k) ((p ^ 2) ^ N)
    rw [g0_pow k, LemTwo.coeff_lgF_odd hp2 k, LemTwo.coeff_g0F_even hp2 N, lg_pow N] at s
    simp only [mul_zero, add_zero, zero_add] at s
    refine ultra (b := α ((p ^ 2) ^ N) * ((p : K) ^ (k + 1))⁻¹) ?_ ?_
      (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ p)))
    · rw [norm_sub_rev]
      exact s
    · rw [norm_mul, np]
      exact mul_le_of_le_one_left (by positivity) (hα _)
  have hB : ∀ m, α m = 0 := by
    intro m
    apply zero_of_bdd _ (max 1 ‖PowerSeries.coeff m (g0F K p)‖)
    intro N
    refine ⟨N + 1, by omega, ?_⟩
    have s := star (p * (p ^ 2) ^ N) m
    rw [g0_pow N, LemTwo.coeff_lgF_odd hp2 N, hA N] at s
    simp only [mul_zero, add_zero, zero_mul] at s
    refine ultra (b := α' (p * (p ^ 2) ^ N) * PowerSeries.coeff m (g0F K p)) s ?_ (le_max_left _ _)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hα' _)).trans (le_max_right _ _)
  have hC : ∀ m, (∀ l, m ≠ (p ^ 2) ^ l) → β m = 0 := by
    intro m hm
    apply zero_of_bdd _ (max 1 ‖PowerSeries.coeff m (g0F K p)‖)
    intro N
    refine ⟨N, le_rfl, ?_⟩
    have s := star ((p ^ 2) ^ N) m
    rw [LemTwo.coeff_g0F_even hp2 N, lg_pow N, lg_zero m hm, hB m] at s
    simp only [mul_zero, zero_mul, add_zero, zero_add] at s
    refine ultra (b := α' ((p ^ 2) ^ N) * PowerSeries.coeff m (g0F K p)) s ?_ (le_max_left _ _)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hα' _)).trans (le_max_right _ _)
  have hD : ∀ l, β ((p ^ 2) ^ l) = β 1 * ((p : K) ^ l)⁻¹ := by
    intro l
    rw [← sub_eq_zero]
    apply zero_of_bdd _ ((p : ℝ) ^ l)
    intro N
    refine ⟨N, le_rfl, ?_⟩
    have s1 := star ((p ^ 2) ^ N) ((p ^ 2) ^ l)
    have s2 := star ((p ^ 2) ^ N) 1
    rw [LemTwo.coeff_g0F_even hp2 N, lg_pow N, LemTwo.coeff_g0F_even hp2 l, lg_pow l, hB] at s1
    rw [LemTwo.coeff_g0F_even hp2 N, lg_pow N, g01, lg1, hB] at s2
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at s1 s2
    have e : (β ((p ^ 2) ^ l) - β 1 * ((p : K) ^ l)⁻¹) * ((p : K) ^ N)⁻¹ =
        (β ((p ^ 2) ^ l) * ((p : K) ^ N)⁻¹ - β' ((p ^ 2) ^ N) * ((p : K) ^ l)⁻¹) -
          ((p : K) ^ l)⁻¹ * (β 1 * ((p : K) ^ N)⁻¹ - β' ((p ^ 2) ^ N)) := by ring
    rw [e]
    have usub : ∀ a b : K, ‖a - b‖ ≤ max ‖a‖ ‖b‖ := fun a b => by
      rw [sub_eq_add_neg]
      have h4 := IsUltrametricDist.norm_add_le_max a (-b)
      rwa [norm_neg] at h4
    refine (usub _ _).trans (max_le ?_ ?_)
    · exact s1.trans (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ p)))
    · rw [norm_mul, np]
      exact mul_le_of_le_one_right (by positivity) s2
  refine ⟨β 1, H - MvPowerSeries.C (β 1) * (at1 0 (lgF K p) * at1 1 (lgF K p)), ?_, by ring⟩
  intro n
  rw [LemTwo.fin_two_vector_eq_matrixVecCons n]
  set i := n 0
  set m := n 1
  rw [map_sub, MvPowerSeries.coeff_C_mul, at1, at1, PowerSeries.coeff_subst_X_zero_subst_mul_X_one, cH,
    hB m]
  have ev0 : (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) m : Fin 2 →₀ ℕ) 0 = i := by simp
  have ev1 : (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) m : Fin 2 →₀ ℕ) 1 = m := by simp
  rw [ev0, ev1]
  have key : β m * PowerSeries.coeff i (lgF K p) -
      β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p)) = 0 := by
    by_cases hm : ∃ l, m = (p ^ 2) ^ l
    · obtain ⟨l, hl⟩ := hm
      rw [hl, hD l, lg_pow l]
      ring
    · push_neg at hm
      rw [hC m hm, lg_zero m hm]
      ring
  have e : 0 * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p) + PowerSeries.coeff i (R m) -
      β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p)) =
      PowerSeries.coeff i (R m) + (β m * PowerSeries.coeff i (lgF K p) -
        β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p))) := by ring
  rw [e, key, add_zero]
  exact hR m i

end Formalism.InvariantFactorPaths.G7
