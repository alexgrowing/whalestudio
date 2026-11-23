import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section Lim

variable {K : Type} [NormedField K]

theorem exists_lim_of_norm_sub_le_pow [CompleteSpace K] {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    {c : ℕ → K} (h : ∀ m n, m ≤ n → ‖c n - c m‖ ≤ r ^ m) : ∃ x, ∀ n, ‖c n - x‖ ≤ r ^ n := by
  have hc : CauchySeq c := by
    refine cauchySeq_of_le_tendsto_0 (fun N => r ^ N) (fun n m N hn hm => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr)
    rw [dist_eq_norm]
    rcases le_total n m with hnm | hnm
    · rw [norm_sub_rev]
      exact (h n m hnm).trans (pow_le_pow_of_le_one hr0 hr.le hn)
    · exact (h m n hnm).trans (pow_le_pow_of_le_one hr0 hr.le hm)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, fun n => ?_⟩
  have ht : Tendsto (fun m => ‖c n - c m‖) atTop (𝓝 ‖c n - x‖) :=
    (tendsto_const_nhds.sub hx).norm
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [norm_sub_rev]
  exact h n m hm

theorem eq_zero_of_norm_le_pow_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {x : K}
    (h : ∀ n, ‖x‖ ≤ r ^ n) : x = 0 :=
  norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr) h)

end Lim

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K]

omit [IsUltrametricDist K] [IsUnitBall O K] [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] in

theorem pow_l_smul_vec_eq (n : ℕ) (v : Vec K a ι) : ((l : O) ^ n) • v = ((l : K) ^ n) • v := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem norm_coeff_pow_l_smul_le {P : PhiMod O K l e a ι} {t : Vec K a ι} (ht : t ∈ P.M) (n : ℕ)
    (τ : ZMod a) (i : ι) (k : ℕ) : ‖coeff k ((((l : K) ^ n) • t) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
  simp only [Pi.smul_apply, coeff_smul, smul_eq_mul, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (mem_A.1 (mem_vecs.1 (mem_tot.1 ht τ) i) k)

theorem pow_l_inv_smul_mem_M {P : PhiMod O K l e a ι} {v : Vec K a ι} {n : ℕ}
    (h : ∀ τ i k, ‖coeff k (v τ i)‖ ≤ ‖(l : K)‖ ^ n) : ((l : K) ^ n)⁻¹ • v ∈ P.M :=
  mem_tot.2 fun τ => mem_vecs.2 fun i => mem_A.2 fun k => by
    simp only [Pi.smul_apply, coeff_smul, smul_eq_mul, norm_mul, norm_inv, norm_pow]
    have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
    rw [inv_mul_le_iff₀ hl, mul_one]
    exact h τ i k

variable [CompleteSpace K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

namespace BKDat

variable (D : BKDat O K l e a ι η H)

theorem mem_Y'_iff_coeff {v : Vec K a ι} : v ∈ D.Y' ↔ E K l e ^ η • v ∈ D.M ∧
    (∀ g, D.desc.act g v = v) ∧ ∀ τ i k, k < e → coeff k (v τ i) = 0 := by
  constructor
  · intro hv
    obtain ⟨y, hy, rfl⟩ := (Descent.mem_Y' _).1 hv
    have h2 := (Descent.mem_invOf _).1 (Descent.Y'_le_Y _ η hv)
    refine ⟨mem_divE.1 h2.1, h2.2, fun τ i k hk => ?_⟩
    show coeff k ((X : K⟦X⟧) ^ e * y τ i) = 0
    rw [coeff_X_pow_mul', if_neg (by omega)]
  · rintro ⟨h1, h2, h3⟩
    have hd : ∀ τ i, (X : K⟦X⟧) ^ e ∣ v τ i := fun τ i => X_pow_dvd_iff.2 fun k hk => h3 τ i k hk
    choose y hy using hd
    have hv : v = (X : K⟦X⟧) ^ e • (y : Vec K a ι) := funext fun τ => funext fun i => hy τ i
    have hXinj : ∀ w w' : Vec K a ι, (X : K⟦X⟧) ^ e • w = (X : K⟦X⟧) ^ e • w' → w = w' :=
      fun w w' h => funext fun τ => funext fun i =>
        mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) (congrFun (congrFun h τ) i)
    refine (Descent.mem_Y' _).2 ⟨y, (Descent.mem_invOf _).2 ⟨mem_divE.2 ?_, fun g => hXinj _ _ ?_⟩, hv.symm⟩
    · refine mem_tot.2 fun τ => mem_vecs.2 fun i => mem_A.2 fun k => ?_
      have := mem_A.1 (mem_vecs.1 (mem_tot.1 h1 τ) i) (k + e)
      have h4 : (E K l e ^ η • v) τ i = (X : K⟦X⟧) ^ e * (E K l e ^ η • y) τ i := by
        rw [hv]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rwa [h4, coeff_X_pow_mul] at this
    · rw [← D.desc.act_X_pow_smul, ← hv, h2 g]

theorem smodEq_Y'_iff (x y : D.Y') (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {(l : O)} ^ n • ⊤ : Submodule O D.Y')] ↔
      ∃ z ∈ D.Y', (x : Vec K a ι) - y = ((l : K) ^ n) • z := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, hb⟩
    refine ⟨b, b.2, ?_⟩
    rw [← pow_l_smul_vec_eq (O := O)]
    exact (congrArg Subtype.val hb).symm
  · rintro ⟨z, hz, h⟩
    refine ⟨⟨z, hz⟩, Submodule.mem_top, Subtype.ext ?_⟩
    show ((l : O) ^ n) • z = (x : Vec K a ι) - y
    rw [pow_l_smul_vec_eq, h]

theorem isHausdorff_Y' : IsHausdorff (Ideal.span {(l : O)}) D.Y' := ⟨fun x hx => by
  have hE : ∀ n τ i k, ‖coeff k ((E K l e ^ η • (x : Vec K a ι)) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
    intro n
    obtain ⟨z, hz, h⟩ := (D.smodEq_Y'_iff x 0 n).1 (hx n)
    rw [ZeroMemClass.coe_zero, sub_zero] at h
    rw [h, smul_comm]
    exact norm_coeff_pow_l_smul_le ((D.mem_Y'_iff_coeff).1 hz).1 n
  have h0 : E K l e ^ η • (x : Vec K a ι) = 0 := funext fun τ => funext fun i => ext fun k =>
    eq_zero_of_norm_le_pow_of_lt_one (norm_nonneg _) (norm_l_lt_one l) fun n => hE n τ i k
  exact Subtype.ext (((isUnit_E (K := K) l e).pow η).smul_left_cancel.1 (h0.trans (smul_zero _).symm))⟩

theorem isPrecomplete_Y' : IsPrecomplete (Ideal.span {(l : O)}) D.Y' := ⟨fun f hf => by
  have hl0 : ∀ n, ((l : K) ^ n) ≠ 0 := fun n => pow_ne_zero _ (l_ne_zero l)
  have hr0 : (0 : ℝ) ≤ ‖(l : K)‖ := norm_nonneg _
  have hr1 : ‖(l : K)‖ < 1 := norm_l_lt_one l
  have hfY : ∀ n, _ := fun n => (D.mem_Y'_iff_coeff).1 (f n).2
  set s : ℕ → Vec K a ι := fun n => E K l e ^ η • (f n : Vec K a ι) with hs_def
  have hs : ∀ m n, m ≤ n → ∀ τ i k, ‖coeff k (s n τ i) - coeff k (s m τ i)‖ ≤ ‖(l : K)‖ ^ m := by
    intro m n hmn τ i k
    obtain ⟨z, hz, h⟩ := (D.smodEq_Y'_iff _ _ m).1 (hf hmn)
    have h' : s m - s n = ((l : K) ^ m) • (E K l e ^ η • z) := by
      simp only [hs_def]
      rw [← smul_sub, h, smul_comm]
    have := norm_coeff_pow_l_smul_le ((D.mem_Y'_iff_coeff).1 hz).1 m τ i k
    rw [← h', Pi.sub_apply, Pi.sub_apply, map_sub] at this
    rwa [norm_sub_rev]
  choose w hw using fun p : ZMod a × ι × ℕ =>
    exists_lim_of_norm_sub_le_pow hr0 hr1 (c := fun n => coeff p.2.2 (s n p.1 p.2.1))
      (fun m n hmn => hs m n hmn p.1 p.2.1 p.2.2)
  set W : Vec K a ι := fun τ i => PowerSeries.mk fun k => w (τ, i, k) with hW_def
  have hW : ∀ n τ i k, ‖coeff k ((s n - W) τ i)‖ ≤ ‖(l : K)‖ ^ n := fun n τ i k => by
    simpa [hW_def] using hw (τ, i, k) n

  have hsinv : ∀ n g, D.desc.act g (s n) = s n := fun n g => by
    simp only [hs_def]
    rw [D.desc.act_E_pow_smul, (hfY n).2.1 g]
  have hWinv : ∀ g, D.desc.act g W = W := fun g => by
    have hsm : ∀ n τ i k, ‖coeff k ((D.desc.act g W - W) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
      intro n
      have hb : ∀ τ i k, ‖coeff k ((W - s n) τ i)‖ ≤ ‖(l : K)‖ ^ n := fun τ i k => by
        rw [Pi.sub_apply, Pi.sub_apply, map_sub, norm_sub_rev, ← map_sub, ← Pi.sub_apply,
          ← Pi.sub_apply]
        exact hW n τ i k
      have ht := pow_l_inv_smul_mem_M (P := D.toPhiMod) hb
      set t := ((l : K) ^ n)⁻¹ • (W - s n) with ht_def
      have hWt : W - s n = ((l : K) ^ n) • t := by rw [ht_def, smul_inv_smul₀ (hl0 n)]
      have : D.desc.act g W - W = ((l : K) ^ n) • (D.desc.act g t - t) := by
        rw [smul_sub, ← map_smul, ← hWt, map_sub, hsinv n g]
        abel
      rw [this]
      exact norm_coeff_pow_l_smul_le (sub_mem (D.desc.act_mem_M g t ht) ht) n
    exact sub_eq_zero.1 (funext fun τ => funext fun i => ext fun k =>
      eq_zero_of_norm_le_pow_of_lt_one hr0 hr1 fun n => hsm n τ i k)
  have hWlow : ∀ τ i, (X : K⟦X⟧) ^ e ∣ W τ i := fun τ i => X_pow_dvd_iff.2 fun k hk => by
    have h0 : coeff k (s 0 τ i) = 0 := by
      have hdv : (X : K⟦X⟧) ^ e ∣ s 0 τ i :=
        Dvd.dvd.mul_left (X_pow_dvd_iff.2 fun k hk => (hfY 0).2.2 τ i k hk) _
      exact X_pow_dvd_iff.1 hdv k hk
    refine eq_zero_of_norm_le_pow_of_lt_one hr0 hr1 fun n => ?_
    have h1 : coeff k (s n τ i) = 0 := by
      have hdv : (X : K⟦X⟧) ^ e ∣ s n τ i :=
        Dvd.dvd.mul_left (X_pow_dvd_iff.2 fun k hk => (hfY n).2.2 τ i k hk) _
      exact X_pow_dvd_iff.1 hdv k hk
    have := hW n τ i k
    rwa [Pi.sub_apply, Pi.sub_apply, map_sub, h1, zero_sub, norm_neg] at this

  obtain ⟨u, hu⟩ := (isUnit_E (K := K) l e).pow η
  set L : Vec K a ι := ((u⁻¹ : K⟦X⟧ˣ) : K⟦X⟧) • W with hL_def
  have hEL : E K l e ^ η • L = W := by
    rw [hL_def, smul_smul, ← hu, Units.mul_inv, one_smul]
  have hLinv : ∀ g, D.desc.act g L = L := fun g => by
    refine ((isUnit_E (K := K) l e).pow η).smul_left_cancel.1 ?_
    rw [← D.desc.act_E_pow_smul, hEL, hWinv g]
  have key : ∀ n, ((l : K) ^ n)⁻¹ • ((f n : Vec K a ι) - L) ∈ D.Y' := fun n => by
    refine (D.mem_Y'_iff_coeff).2 ⟨?_, fun g => ?_, fun τ i k hk => ?_⟩
    · rw [smul_comm, smul_sub, hEL]
      exact pow_l_inv_smul_mem_M (hW n)
    · rw [map_smul, map_sub, (hfY n).2.1 g, hLinv g]
    · have hdv : (X : K⟦X⟧) ^ e ∣ (((l : K) ^ n)⁻¹ • ((f n : Vec K a ι) - L)) τ i := by
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_C_mul]
        refine Dvd.dvd.mul_left (dvd_sub (X_pow_dvd_iff.2 fun k hk => (hfY n).2.2 τ i k hk) ?_) _
        simp only [hL_def, Pi.smul_apply, smul_eq_mul]
        exact Dvd.dvd.mul_left (hWlow τ i) _
      exact X_pow_dvd_iff.1 hdv k hk
  have hLmem : L ∈ D.Y' := by
    have := sub_mem (f 0).2 (key 0)
    rwa [pow_zero, inv_one, one_smul, sub_sub_cancel] at this
  refine ⟨⟨L, hLmem⟩, fun n => (D.smodEq_Y'_iff _ _ n).2 ⟨_, key n, ?_⟩⟩
  exact (smul_inv_smul₀ (hl0 n) _).symm⟩

end BKDat

theorem BKDat.isAdicComplete_Y' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H),
    IsAdicComplete (Ideal.span {(l : O)}) D.Y' := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact { toIsHausdorff := D.isHausdorff_Y', toIsPrecomplete := D.isPrecomplete_Y' }

end GlobalTheory.BK
