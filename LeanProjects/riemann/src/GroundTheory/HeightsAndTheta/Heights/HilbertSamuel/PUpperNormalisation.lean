import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUpperNormalisation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology

noncomputable section

namespace UpperNormalisation

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, mConeMap, aeval_C]
    have e : (algebraMap ℤ (MvPolynomial K Ω) (n : ℤ)) = C ((n : ℕ) : Ω) := by simp
    rw [e, hn, C_0]
  have hh : (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ := h.2.2.1
  have : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hmem
  rw [hh, Ideal.mem_bot] at this
  exact_mod_cast this

theorem exists_coord_ne_zero {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

theorem secM_le_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) {d : K → ℕ}
    (hd : ∀ k, (d k : ℤ) = τ * a k) : secM y d ≤ chartLat y a τ := by
  intro s hs
  have hle : Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = s} ≤
      (chartLat y a τ).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩ c _
    have key : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
      conv_lhs => rw [g.as_sum]
      conv_rhs => rw [g.as_sum]
      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib, mul_assoc]
      congr 2
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = ∏ i, (y ⟨k, c k⟩)⁻¹ ^ m ⟨k, i⟩
      rw [Finset.prod_pow_eq_pow_sum, hg m hm k, ← hd k, zpow_neg, zpow_natCast, inv_pow]
    rw [key, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨g, rfl⟩
  exact hle hs

end UpperNormalisation

open UpperNormalisation Mono in

theorem UpperNormalisation.proof (h7 : G7.Statement) (hPack : PackingStatement) (hCond : KH.CondStatement) :
    UpperNormalisation.Statement := by
  intro K _ ι _ Ω _ y D B P0 II hD hII har hb hsg hconj hBa ε hε
  have : CharZero Ω := charZero_of_isArithVar har
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _

  set a : K → ℕ := fun k => (B.a k).toNat with hadef
  have ha : ∀ k, (a k : ℤ) = B.a k := fun k => Int.toNat_of_nonneg (by linarith [hBa k])
  have ha1 : ∀ k, 1 ≤ a k := fun k => by have := hBa k; have := ha k; omega
  have hBa' : B.a = fun k => (a k : ℤ) := funext fun k => (ha k).symm

  obtain ⟨k0, c, hc, hc0, hcs⟩ := hCond K ι Ω y a ha1 (exists_coord_ne_zero har) hb
  obtain ⟨q, w, hw, hgen, hwsm⟩ := hsg.gen
  have hcy : aeval y c ∈ chartLat y B.a k0 :=
    secM_le_chartLat y B.a k0 (d := fun κ => k0 * a κ) (fun κ => by push_cast; rw [ha])
      (Submodule.subset_span ⟨c, hc, rfl⟩)
  obtain ⟨Cc, hCc⟩ := SectionBounded.proof K ι Ω y B q w hw hgen hwsm k0 (aeval y c) hcy

  set Ib := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hIb
  set G := geomDeg (mCoordIdeal y) B D with hG
  set η : ℝ := ε / (4 * (((D : ℝ) + 1) * (|G| + 1))) with hηdef
  have hη : 0 < η := by positivity
  set B' := HermLine.constShift B (-η) with hB'def
  have hB'a : B'.a = B.a := constShift_a B (-η)
  have hB'h : ∀ z, B'.h z = Real.exp η * B.h z := fun z => by
    show B.h z * Real.exp (-(-η)) = _
    rw [neg_neg, mul_comm]
  have hB'sm : IsSmoothHerm B' := (semipos_constShift hsg.semipos (-η)).1
  obtain ⟨hfin, Cp, hCp⟩ := hPack K ι Ω y D B' (chartLat y B'.a) har hb hB'sm
    (fun τ => chartLat_le_nm y B'.a τ)
  have hG7 := h7 K ι Ω y D B' P0 II hD hII har hb (smallGen_constShift hsg (by linarith))
    (conj_constShift hconj (-η))
  have hCS := ConstantShift.proof K ι (II K ι) (mCoordIdeal y) D B (-η) (hII K ι) har hsg.semipos.1
  have hI' : II K ι (mCoordIdeal y) (D + 1) (fun _ => B') ≤ Ib + ε / 4 := by
    rw [hCS]
    have h1 : ((D : ℝ) + 1) * η * G ≤ ((D : ℝ) + 1) * η * (|G| + 1) :=
      mul_le_mul_of_nonneg_left ((le_abs_self G).trans (by linarith)) (by positivity)
    have h2 : ((D : ℝ) + 1) * η * (|G| + 1) = ε / 4 := by
      rw [hηdef]; field_simp
    linarith

  set v : ℕ → ℝ := fun n => smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) n /
    ((n : ℝ) ^ (D + 1) / F) with hv
  have hv_bdd : ∀ n, v n ≤ |Cp| * F * 2 ^ (D + 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv]
      simp only [Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, div_zero]
      positivity
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) / F := by positivity
      rw [hv]
      dsimp only
      rw [div_le_iff₀ hnpos]
      have h1 := (hCp n).trans (mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity))
      have h2 : ((n : ℝ) + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      calc _ ≤ |Cp| * ((n : ℝ) + 1) ^ (D + 1) := h1
        _ ≤ |Cp| * (2 * n) ^ (D + 1) := mul_le_mul_of_nonneg_left h2 (abs_nonneg Cp)
        _ = |Cp| * F * 2 ^ (D + 1) * ((n : ℝ) ^ (D + 1) / F) := by
          rw [mul_pow]
          field_simp
  have hvB : IsBoundedUnder (· ≤ ·) atTop v := isBoundedUnder_of ⟨_, hv_bdd⟩
  have hev1 : ∀ᶠ m in atTop, v m < Ib + ε / 2 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt (hG7.trans hI') (by linarith)) hvB

  have hcmp : ∀ n : ℕ, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) →
      smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) := by
    intro n hCn
    refine smallSectionCount_le_of_injOn (Q := fun m => IsSmallH (mCoordIdeal y) y B' (m + k0))
      (La' := fun m => chartLat y B'.a (m + k0)) (fun s => aeval y c * s)
      (fun s _ t _ hst => mul_left_cancel₀ hc0 hst) (fun s hs hsm => ⟨?_, ?_⟩) (hfin (n + k0))
    · have hs' : s ∈ chartLatNm y (fun κ => (a κ : ℤ)) n := by rw [← hBa']; exact hs
      have := hcs n s hs'
      show aeval y c * s ∈ chartLat y B'.a (n + k0)
      rw [hB'a]
      exact secM_le_chartLat y B.a (n + k0) (fun κ => by push_cast; rw [ha]) this
    · intro dg dh g h z hg hh hd he hz
      rw [hB'a] at hd
      have hch : IsMultiHomog (c * h) ((fun κ => k0 * a κ) + dh) := SectionBounded.homog_mul hc hh
      have h1 := hsm dg ((fun κ => k0 * a κ) + dh) g (c * h) z hg hch
        (fun κ => by simp only [Pi.add_apply]; push_cast; rw [hd κ, ha]; push_cast; ring)
        (by rw [he, map_mul]; ring) hz
      have h2 := hCc (fun κ => k0 * a κ) 0 c 1 z hc SectionBounded.homog_one
        (fun κ => by simp only [Pi.zero_apply]; push_cast; rw [ha]; ring) (by rw [map_one, mul_one]) hz
      rw [map_one, map_one, norm_one, mul_one] at h2
      have hBz : 0 ≤ B.h z := (B.pos z hz.1).le
      rw [map_mul, eval_mul, norm_mul] at h1
      rw [hB'h, mul_pow, ← Real.exp_nat_mul, pow_add]
      have hhn : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := by positivity
      calc ‖eval z (map (Int.castRingHom ℂ) g)‖
          ≤ ‖eval z (map (Int.castRingHom ℂ) c)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := h1
        _ ≤ Cc * B.h z ^ k0 * ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := by
          rw [mul_assoc, mul_assoc (Cc * _)]
          exact mul_le_mul_of_nonneg_right h2 hhn
        _ ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) * B.h z ^ k0 * ‖eval z (map (Int.castRingHom ℂ) h)‖ *
            B.h z ^ n := by
          gcongr
        _ = _ := by
          rw [show ((n + k0 : ℕ) : ℝ) * η = η * ((n + k0 : ℕ) : ℝ) from mul_comm _ _]
          ring

  have hlim : Tendsto (fun n : ℕ => (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1)) atTop (𝓝 (Ib + ε / 2)) := by
    have h0 : Tendsto (fun n : ℕ => (k0 : ℝ) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul (Ib + ε / 2)
  have hev3 : ∀ᶠ n : ℕ in atTop, (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1) < Ib + ε :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ n : ℕ in atTop, v (n + k0) < Ib + ε / 2 :=
    (tendsto_add_atTop_nat k0).eventually hev1
  have hevC : ∀ᶠ n : ℕ in atTop, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (⌈|Cc| / η⌉₊)] with n hn
    have h1 : |Cc| / η ≤ ((n + k0 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈|Cc| / η⌉₊ ≤ n + k0 by omega))
    have h2 : |Cc| ≤ η * ((n + k0 : ℕ) : ℝ) := by rw [div_le_iff₀ hη] at h1; linarith
    have h3 := Real.add_one_le_exp (η * ((n + k0 : ℕ) : ℝ))
    linarith [le_abs_self Cc]
  filter_upwards [hev2, hev3, hevC, eventually_ge_atTop 1] with n h2 h3 hC hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmpos : (0 : ℝ) < ((n + k0 : ℕ) : ℝ) ^ (D + 1) / F := by
    have : (0 : ℝ) < ((n + k0 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + k0 by omega)
    positivity
  have hcount : smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) ≤
      (Ib + ε / 2) * (((n + k0 : ℕ) : ℝ) ^ (D + 1) / F) := by
    have := h2
    rw [hv] at this
    dsimp only at this
    rw [div_lt_iff₀ hmpos] at this
    exact this.le
  have hratio : ((n + k0 : ℕ) : ℝ) ^ (D + 1) = (1 + (k0 : ℝ) / n) ^ (D + 1) * (n : ℝ) ^ (D + 1) := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp
  calc smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n
      ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) := hcmp n hC
    _ ≤ (Ib + ε / 2) * (((n + k0 : ℕ) : ℝ) ^ (D + 1) / F) := hcount
    _ = ((Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1)) * ((n : ℝ) ^ (D + 1) / F) := by
      rw [hratio]; ring
    _ ≤ (Ib + ε) * ((n : ℝ) ^ (D + 1) / F) :=
      mul_le_mul_of_nonneg_right h3.le (by positivity)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
