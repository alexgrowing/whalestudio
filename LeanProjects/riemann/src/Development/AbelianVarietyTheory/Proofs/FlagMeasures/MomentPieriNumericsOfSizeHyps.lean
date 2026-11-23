import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SizeNum

private lemma sqrt_two_mul_succ_le (r : ℕ) (n : ℝ) (hn : 2 * ((r : ℝ) + 1) ≤ n) :
    Real.sqrt (2 * ((r : ℝ) + 1)) ≤ n := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  calc Real.sqrt (2 * ((r : ℝ) + 1)) ≤ Real.sqrt (n ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = n := Real.sqrt_sq (by linarith)

theorem aOf_ge (r : ℕ) (n h : ℝ) (hn : 2 * ((r : ℝ) + 1) ≤ n) (hh : n ^ 19 / 4 ≤ h) :
    n ^ 18 / 32 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := by
  have hs := sqrt_two_mul_succ_le r n hn
  have hr : (0 : ℝ) < 2 * ((r : ℝ) + 1) := by positivity
  have hsp : 0 < Real.sqrt (2 * ((r : ℝ) + 1)) := Real.sqrt_pos.mpr hr
  have hn0 : 0 ≤ n := by linarith
  unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
  rw [le_div_iff₀ (by positivity)]
  calc n ^ 18 / 32 * (8 * Real.sqrt (2 * ((r : ℝ) + 1))) ≤ n ^ 18 / 32 * (8 * n) := by gcongr
    _ = n ^ 19 / 4 := by ring
    _ ≤ h := hh

theorem AG_le (k r : ℕ) (n : ℝ) (hn : n = 2 * r + k + 1) :
    0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * n ^ 2 := by
  subst hn
  unfold Formalism.FourierDecayAlt.ThreeDimData.AG
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  constructor
  · positivity
  · nlinarith [mul_le_mul (show (k : ℝ) + r ≤ 2 * r + k + 1 by linarith)
      (show (r : ℝ) + 1 ≤ 2 * r + k + 1 by linarith) (by positivity) (by positivity)]

theorem AS_le (k r : ℕ) (n : ℝ) (hn : n = 2 * r + k + 1) :
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * n ^ 3 := by
  subst hn
  unfold Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hd0 : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 := by nlinarith
  have hd1 : (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 ≤
      2 * (2 * (r : ℝ) + k + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul (show (2 : ℝ) * r + k ≤ 2 * r + k + 1 by linarith) hd1 hd0 (by positivity)]

theorem pow_big (n : ℝ) (hn : 1000 ≤ n) : 1000 * n ^ 5 ≤ n ^ 18 / 32 ∧ n ^ 3 ≤ n ^ 5 ∧ n ^ 2 ≤ n ^ 5 ∧
    n ^ 4 ≤ n ^ 5 ∧ 1 ≤ n ^ 5 ∧ n ^ 18 ≤ n ^ 19 := by
  have h1 : (1 : ℝ) ≤ n := by linarith
  have h5 : 0 ≤ n ^ 5 := by positivity
  have h13 : (32000 : ℝ) ≤ n ^ 13 := by
    calc (32000 : ℝ) ≤ 1000 ^ 13 := by norm_num
      _ ≤ n ^ 13 := by gcongr
  refine ⟨?_, pow_le_pow_right₀ h1 (by norm_num), pow_le_pow_right₀ h1 (by norm_num),
    pow_le_pow_right₀ h1 (by norm_num), one_le_pow₀ h1, pow_le_pow_right₀ h1 (by norm_num)⟩
  have e : n ^ 18 = n ^ 13 * n ^ 5 := by ring
  rw [e]
  nlinarith

theorem gapOK (k r : ℕ) (n : ℝ) (hn : n = 2 * r + k + 1) (hk : 1 ≤ k) (hb : 1000 ≤ n) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (n ^ 19 / 4) ∧ GapCell k r (n ^ 19 / 2) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn2 : 2 * ((r : ℝ) + 1) ≤ n := by rw [hn]; linarith
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := pow_big n hb
  have h19 : 0 ≤ n ^ 19 := by positivity
  have h18 : 0 ≤ n ^ 18 := by positivity
  have hn0 : 0 ≤ n := by linarith
  have ha4 := aOf_ge r n (n ^ 19 / 4) hn2 le_rfl
  have ha2 := aOf_ge r n (n ^ 19 / 2) hn2 (by linarith)
  obtain ⟨hG0, hG⟩ := AG_le k r n hn
  have hS := AS_le k r n hn
  have hrn : (r : ℝ) + 1 ≤ n := by linarith
  have h23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsum : Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 6 * n ^ 3 := by linarith
  have hM0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r := by unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity
  have hM : Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ 2 * n ^ 2 := by unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; nlinarith
  have hMS : Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤ 12 * n ^ 5 := by
    calc Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)
        ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (6 * n ^ 3) := mul_le_mul_of_nonneg_left hsum hM0
      _ ≤ 2 * n ^ 2 * (6 * n ^ 3) := mul_le_mul_of_nonneg_right hM (by positivity)
      _ = 12 * n ^ 5 := by ring
  have h9 : ((r : ℝ) + 1) * n ^ 2 ≤ n ^ 5 := by
    calc ((r : ℝ) + 1) * n ^ 2 ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right hrn (by positivity)
      _ = n ^ 3 := by ring
      _ ≤ n ^ 5 := hb2
  have hC : ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤ 6 * n ^ 5 := by
    have hr2 : ((r : ℝ) + 1) ^ 2 ≤ n ^ 2 := by gcongr
    calc ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)
        ≤ ((r : ℝ) + 1) ^ 2 * (6 * n ^ 3) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ n ^ 2 * (6 * n ^ 3) := mul_le_mul_of_nonneg_right hr2 (by positivity)
      _ = 6 * n ^ 5 := by ring
  constructor
  · unfold Formalism.FourierDecayAlt.ThreeDimData.GapOK
    rw [hcast]
    refine ⟨hk, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  · unfold GlobalTheory.CellAmp.GapCell
    linarith

theorem lam_lt (D : D7) (τ : D.what₂.Tau) (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : a.val < D.R.k - 1) :
    lamD D τ a = ((D.hc τ).v ⟨a.val, h⟩ : ℝ) := by
  show lamS D.R (D.hc τ) (Fin.cast (dimS_eq D.R) a) = _
  unfold lamS
  rw [dif_pos (show (Fin.cast (dimS_eq D.R) a).val < D.R.k - 1 from h)]
  rfl

theorem lam_ge (D : D7) (τ : D.what₂.Tau) (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : ¬ a.val < D.R.k - 1)
    (h' : a.val - (D.R.k - 1) < D.R.m) :
    lamD D τ a = -((D.hc τ).b ⟨a.val - (D.R.k - 1), h'⟩ : ℝ) := by
  show lamS D.R (D.hc τ) (Fin.cast (dimS_eq D.R) a) = _
  unfold lamS
  rw [dif_neg (show ¬ (Fin.cast (dimS_eq D.R) a).val < D.R.k - 1 from h),
    dif_pos (show (Fin.cast (dimS_eq D.R) a).val - (D.R.k - 1) < D.R.m from h')]
  rfl

theorem lam_v (D : D7) (τ : D.what₂.Tau) (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : a.val < D.R.k - 1) :
    lamD D τ a = vOne D τ (a.val + 1) := by
  rw [lam_lt D τ a h]
  unfold vOne
  rw [dif_pos (show 1 ≤ a.val + 1 ∧ a.val + 1 ≤ D.R.k - 1 by omega)]
  simp

theorem lam_b (D : D7) (τ : D.what₂.Tau) (a : Fin (2 * D.R.rS + D.R.k + 1)) (j : ℕ) (hj : 1 ≤ j)
    (h : a.val + 2 = D.R.k + j) : lamD D τ a = -bOne D τ j := by
  have hk := D.R.m_add_three_le_k
  have hge : ¬ a.val < D.R.k - 1 := by omega
  by_cases hjm : j ≤ D.R.m
  · have h' : a.val - (D.R.k - 1) < D.R.m := by omega
    rw [lam_ge D τ a hge h']
    unfold bOne
    rw [dif_pos (show 1 ≤ j ∧ j ≤ D.R.m from ⟨hj, hjm⟩)]
    have e : (⟨a.val - (D.R.k - 1), h'⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ :=
      Fin.ext (show a.val - (D.R.k - 1) = j - 1 by omega)
    rw [e]
  · show lamS D.R (D.hc τ) (Fin.cast (dimS_eq D.R) a) = _
    unfold lamS bOne
    rw [dif_neg (show ¬ (Fin.cast (dimS_eq D.R) a).val < D.R.k - 1 from hge),
      dif_neg (show ¬ ((Fin.cast (dimS_eq D.R) a).val - (D.R.k - 1) < D.R.m) from
        (by omega : ¬ (a.val - (D.R.k - 1) < D.R.m))),
      dif_neg (show ¬ (1 ≤ j ∧ j ≤ D.R.m) by omega)]
    simp

private theorem two_mul_rS_add_k_add_one_eq (R : Formalism.BasicNotions.Ranks) : 2 * R.rS + R.k + 1 = R.k + R.m - 1 := by
  obtain ⟨t, ht⟩ := R.m_even
  have h2 := R.two_le_m
  unfold Formalism.BasicNotions.Ranks.rS
  omega

private theorem lam_antitone_of_isDominant_liftWt {n : ℕ} (f : Fin n → ℝ)
    (hf : ∀ (a : Fin n) (h : a.val + 1 < n), f ⟨a.val + 1, h⟩ < f a) : StrictAnti f := by
  intro a c hac
  obtain ⟨c, hc⟩ := c
  have hac' : a.val < c := hac
  induction c with
  | zero => omega
  | succ c ih =>
    by_cases h : a.val < c
    · exact lt_trans (hf ⟨c, by omega⟩ hc) (ih (by omega) (Fin.lt_def.mpr h) h)
    · have e : a = ⟨c, by omega⟩ := Fin.ext (show a.val = c by omega)
      rw [e]
      exact hf ⟨c, by omega⟩ hc

theorem num_of_size : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ (τ : D.what₂.Tau) (w : D.what₂.Word) (U : ℕ → ℝ), (∀ i : Fin D.R.k, U (i.val + 1) = uS D w τ i) → Num D.R.k D.R.rS (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) ∧ GapCell D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) ∧ PI.BesselPeriodGGP.eps48 D.R.k D.R.rS = epsSH D.R := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w U hU
  obtain ⟨hS0, hD0, -⟩ := hZ
  obtain ⟨-, -, hm4f, -, -, -, -, hbj, -, -, -, -, -, -, -, hbpow, hbm, hu1, -, -, hnode, hgap, -,
    hClm, hCl0⟩ := hS0
  obtain ⟨hv, -⟩ := hD0
  have hm2 := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hdim : 2 * D.R.rS + D.R.k + 1 = D.R.r := (two_mul_rS_add_k_add_one_eq D.R).trans hr.symm
  have hmR : (1000 : ℝ) ≤ D.R.m := hCl.trans hClm
  have hMK : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hNr : (D.R.r : ℝ) = D.R.k + D.R.m - 1 := by
    have h : D.R.r + 1 = D.R.k + D.R.m := by rw [hr]; omega
    have h' : ((D.R.r + 1 : ℕ) : ℝ) = ((D.R.k + D.R.m : ℕ) : ℝ) := by rw [h]
    push_cast at h'
    linarith
  have hK : (1003 : ℝ) ≤ D.R.k := by
    have : ((D.R.m + 3 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast hk3
    push_cast at this
    linarith
  have hN1000 : (1000 : ℝ) ≤ D.R.r := by linarith
  have hKN : (D.R.k : ℝ) ≤ D.R.r := by linarith
  have hMN : (D.R.m : ℝ) ≤ D.R.r := by linarith
  have hN0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hNeq : (D.R.r : ℝ) = 2 * D.R.rS + D.R.k + 1 := by
    have : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = D.R.r := by rw [hdim]
    push_cast at this
    linarith
  have hL1 : 1 ≤ large₂.sc.L := by
    show 1 ≤ large₂.sc.x ^ large₂.sc.eps
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb1 : 1 ≤ large₂.sc.b := by
    show 1 ≤ Real.exp large₂.sc.L
    exact Real.one_le_exp (by linarith)
  have hF1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hm4f
    exact_mod_cast this

  have hp : 0 ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 :=
    mul_nonneg (mul_nonneg hCl0.le (Nat.cast_nonneg _)) (by positivity)
  have hp' : 0 ≤ (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
  have hcons : ∀ (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : a.val + 1 < 2 * D.R.rS + D.R.k + 1),
      Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 <
        lamD D τ a - lamD D τ ⟨a.val + 1, h⟩ := by
    intro a h
    have h' : (Fin.cast (dimS_eq D.R) a).val + 1 < D.R.r := by
      show a.val + 1 < D.R.r
      omega
    exact hgap τ (Fin.cast (dimS_eq D.R) a) h'
  have hanti : StrictAnti (lamD D τ) := by
    apply lam_antitone_of_isDominant_liftWt
    intro a h
    have := hcons a h
    linarith
  have hUi : ∀ (j : ℕ) (h : j < D.R.k), U (j + 1) = ((D.hcW w τ).u ⟨j, h⟩ : ℝ) :=
    fun j h => hU ⟨j, h⟩
  have hlamFirst : lamD D τ ⟨D.R.k - 1, by omega⟩ = -bOne D τ 1 :=
    lam_b D τ _ 1 le_rfl (show D.R.k - 1 + 2 = D.R.k + 1 by omega)
  have hlamLast : lamD D τ ⟨2 * D.R.rS + D.R.k, by omega⟩ = -bOne D τ D.R.m :=
    lam_b D τ _ D.R.m (by omega) (show 2 * D.R.rS + D.R.k + 2 = D.R.k + D.R.m by omega)

  have hint : ∀ a : Fin (2 * D.R.rS + D.R.k + 1), ∃ z : ℤ, lamD D τ a = z := by
    intro a
    have := a.isLt
    by_cases h1 : a.val < D.R.k - 1
    · obtain ⟨z, hz⟩ := (D.hc τ).v_int ⟨a.val, h1⟩
      exact ⟨z, by rw [lam_lt D τ a h1, hz]; norm_cast⟩
    · have h2 : a.val - (D.R.k - 1) < D.R.m := by omega
      obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨a.val - (D.R.k - 1), h2⟩
      exact ⟨-z, by rw [lam_ge D τ a h1 h2, hz]; norm_cast⟩
  have hC2 : Formalism.QuantumDeterminants.IsHCParam (lamD D τ) := by
    refine ⟨hanti, fun a => ?_⟩
    obtain ⟨z, hz⟩ := hint a
    obtain ⟨t, ht⟩ := D.R.k_even
    refine ⟨z - D.R.rS - t, ?_⟩
    rw [hz]
    have hkt : (D.R.k : ℝ) = t + t := by exact_mod_cast ht
    push_cast
    rw [hkt]
    ring
  have hC3 : ∀ a : Fin (2 * D.R.rS + D.R.k + 1), ∀ i ∈ Finset.Icc 1 D.R.k,
      ∃ z : ℤ, lamD D τ a - U i = (z : ℝ) + 1 / 2 := by
    intro a i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    obtain ⟨z1, hz1⟩ := hint a
    obtain ⟨z2, hz2⟩ := (D.hcW w τ).u_half ⟨j, by omega⟩
    refine ⟨z1 - z2 - 1, ?_⟩
    rw [hUi j (by omega), hz1, hz2]
    push_cast
    ring
  have hC4 : ∀ a : Fin (2 * D.R.rS + D.R.k + 1), a.val < D.R.k → lamD D τ a < U (a.val + 1) := by
    intro a ha
    rw [hUi a.val ha]
    by_cases h1 : a.val < D.R.k - 1
    · rw [lam_lt D τ a h1]
      have := (D.hcW w τ).u_gt_v ⟨a.val, h1⟩
      rw [D.hcW_v w τ] at this
      exact_mod_cast this
    · have h2 : a.val - (D.R.k - 1) < D.R.m := by omega
      rw [lam_ge D τ a h1 h2]
      have e1 : (⟨a.val - (D.R.k - 1), h2⟩ : Fin D.R.m) = ⟨0, by omega⟩ :=
        Fin.ext (show a.val - (D.R.k - 1) = 0 by omega)
      have e2 : (⟨a.val, ha⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ :=
        Fin.ext (show a.val = D.R.k - 1 by omega)
      rw [e1, e2]
      have := (D.hcW w τ).u_last_gt (by omega) (by omega)
      rw [D.hcW_b w τ] at this
      exact_mod_cast this
  have hC5 : ∀ a : Fin (2 * D.R.rS + D.R.k + 1), a.val + 1 < D.R.k → U (a.val + 2) < lamD D τ a := by
    intro a ha
    have h1 : a.val < D.R.k - 1 := by omega
    rw [show a.val + 2 = (a.val + 1) + 1 by omega, hUi (a.val + 1) ha, lam_lt D τ a h1]
    have := (D.hcW w τ).v_gt_u ⟨a.val, h1⟩
    rw [D.hcW_v w τ] at this
    exact_mod_cast this
  have hvb : 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) * 8 ≤ bOne D τ 1 := by
    have hv1 := hv τ 1 le_rfl (by omega)
    have hb := hbj τ 1 le_rfl (by omega)
    have hKD : 0 ≤ (D.R.k : ℝ) * (D.s.Del : ℝ) := by linarith [hv1.1, hv1.2]
    have hCM : 32 ≤ Cl * (D.R.m : ℝ) := by
      calc (32 : ℝ) ≤ 1000 * 1000 := by norm_num
        _ ≤ Cl * (D.R.m : ℝ) := mul_le_mul hCl hmR (by norm_num) (by linarith)
    linarith [mul_le_mul_of_nonneg_right hCM hKD]
  have hC6 : ∀ a : Fin (2 * D.R.rS + D.R.k + 1), a.val + 1 < D.R.k →
      0 ≤ lamD D τ a ∧ lamD D τ a ≤ bOne D τ 1 / 8 := by
    intro a ha
    rw [lam_v D τ a (by omega)]
    have := hv τ (a.val + 1) (by omega) (by omega)
    exact ⟨this.1, by linarith [this.2, hvb]⟩
  have hC7 : ∀ a : Fin (2 * D.R.rS + D.R.k + 1), D.R.k ≤ a.val + 1 →
      -2 * bOne D τ 1 ≤ lamD D τ a ∧ lamD D τ a ≤ -bOne D τ 1 := by
    intro a ha
    have := a.isLt
    have hlo : lamD D τ ⟨2 * D.R.rS + D.R.k, by omega⟩ ≤ lamD D τ a :=
      hanti.antitone (Fin.le_iff_val_le_val.mpr (show a.val ≤ 2 * D.R.rS + D.R.k by omega))
    have hhi : lamD D τ a ≤ lamD D τ ⟨D.R.k - 1, by omega⟩ :=
      hanti.antitone (Fin.le_iff_val_le_val.mpr (show D.R.k - 1 ≤ a.val by omega))
    rw [hlamLast] at hlo
    rw [hlamFirst] at hhi
    have := hbm τ
    constructor <;> linarith
  have hbB : large₂.sc.b ^ (2 : ℝ) ≤ large₂.sc.b ^ max 2 Cu :=
    Real.rpow_le_rpow_of_exponent_le hb1 (le_max_left _ _)
  have hbB' : large₂.sc.b ^ Cu ≤ large₂.sc.b ^ max 2 Cu :=
    Real.rpow_le_rpow_of_exponent_le hb1 (le_max_right _ _)
  have hC8 : ∀ a : Fin (2 * D.R.rS + D.R.k + 1), |lamD D τ a| ≤ large₂.sc.b ^ max 2 Cu := by
    intro a
    have := a.isLt
    have hlo : lamD D τ ⟨2 * D.R.rS + D.R.k, by omega⟩ ≤ lamD D τ a :=
      hanti.antitone (Fin.le_iff_val_le_val.mpr (show a.val ≤ 2 * D.R.rS + D.R.k by omega))
    have hhi : lamD D τ a ≤ lamD D τ ⟨0, by omega⟩ :=
      hanti.antitone (Fin.le_iff_val_le_val.mpr (show 0 ≤ a.val by omega))
    rw [hlamLast] at hlo
    have h0 := hC6 ⟨0, by omega⟩ (show 0 + 1 < D.R.k by omega)
    have hm := (hbpow τ D.R.m (by omega) le_rfl).2
    have h1 := (hbpow τ 1 le_rfl (by omega)).2
    rw [abs_le]
    constructor <;> linarith [h0.1, h0.2]
  have hu0 : ((D.hcW w τ).u ⟨0, by omega⟩ : ℝ) ≤ large₂.sc.b ^ Cu := by
    have := hu1 w τ
    unfold uOne at this
    rw [dif_pos (show 1 ≤ 1 ∧ 1 ≤ D.R.k by omega)] at this
    exact this
  have hC9 : ∀ i ∈ Finset.Icc 1 D.R.k, |U i| ≤ large₂.sc.b ^ max 2 Cu := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hjn : j < 2 * D.R.rS + D.R.k + 1 := by omega
    have hlow : lamD D τ ⟨j, hjn⟩ < U (j + 1) := hC4 ⟨j, hjn⟩ (show j < D.R.k by omega)
    have h8 := hC8 ⟨j, hjn⟩
    rw [abs_le] at h8 ⊢
    refine ⟨by linarith [h8.1], ?_⟩
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [hUi 0 (by omega)]
      linarith
    · have hj' : j - 1 < 2 * D.R.rS + D.R.k + 1 := by omega
      have hup : U (j - 1 + 2) < lamD D τ ⟨j - 1, hj'⟩ :=
        hC5 ⟨j - 1, hj'⟩ (show j - 1 + 1 < D.R.k by omega)
      rw [show j - 1 + 2 = j + 1 by omega] at hup
      have h8' := (abs_le.mp (hC8 ⟨j - 1, hj'⟩)).2
      linarith
  have hC10 : ∀ a c : Fin (2 * D.R.rS + D.R.k + 1), a < c → c.val + 1 < D.R.k →
      (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 ≤ lamD D τ a - lamD D τ c := by
    intro a c hac _
    have hlt : a.val < c.val := hac
    have hc := c.isLt
    have ha1 : a.val + 1 < 2 * D.R.rS + D.R.k + 1 := by omega
    have key := hcons a ha1
    have hmono : lamD D τ c ≤ lamD D τ ⟨a.val + 1, ha1⟩ :=
      hanti.antitone (Fin.le_iff_val_le_val.mpr (show a.val + 1 ≤ c.val by omega))
    linarith

  have hKpow : (D.R.k : ℝ) ^ 1000 ≤ (D.R.k : ℝ) ^ Cl := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ D.R.k) hCl
    rwa [show (1000 : ℝ) = ((1000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hb1K : (D.R.k : ℝ) ^ Cl ≤ bOne D τ 1 :=
    le_trans (le_max_left _ _) (hbpow τ 1 le_rfl (by omega)).1
  have hNK : (D.R.r : ℝ) ≤ (D.R.k : ℝ) * D.R.k := by
    have := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ D.R.k by linarith) (show (0 : ℝ) ≤ D.R.k by linarith)
    linarith
  have hbig19 : (D.R.r : ℝ) ^ 19 ≤ bOne D τ 1 := by
    calc (D.R.r : ℝ) ^ 19 ≤ ((D.R.k : ℝ) * D.R.k) ^ 19 := by gcongr
      _ = (D.R.k : ℝ) ^ 38 := by ring
      _ ≤ (D.R.k : ℝ) ^ 1000 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ _ := hKpow.trans hb1K
  have hC15 : 10 ^ 6 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 ≤ bOne D τ 1 := by
    rw [hdim]
    have h1 : (10 : ℝ) ^ 6 ≤ (D.R.k : ℝ) ^ 2 := by
      calc (10 : ℝ) ^ 6 ≤ 1003 ^ 2 := by norm_num
        _ ≤ (D.R.k : ℝ) ^ 2 := by gcongr
    have h2 : (D.R.r : ℝ) ^ 7 ≤ ((D.R.k : ℝ) * D.R.k) ^ 7 := by gcongr
    calc (10 : ℝ) ^ 6 * (D.R.r : ℝ) ^ 7 ≤ (D.R.k : ℝ) ^ 2 * ((D.R.k : ℝ) * D.R.k) ^ 7 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (D.R.k : ℝ) ^ 16 := by ring
      _ ≤ (D.R.k : ℝ) ^ 1000 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ _ := hKpow.trans hb1K
  have hnode19 : (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have hF5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hF1
    have h1 : 1 ≤ Cl * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hF5) hL1
    have h19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
    calc (D.R.r : ℝ) ^ 19 = 1 * (D.R.r : ℝ) ^ 19 := by ring
      _ ≤ (Cl * (D.R.f : ℝ) ^ 5 * large₂.sc.L) * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right h1 h19
      _ = _ := by ring
  have hnodeGap : ∀ a c : Fin (2 * D.R.rS + D.R.k + 1), a < c → ¬ a.val < D.R.k - 1 →
      (D.R.r : ℝ) ^ 19 ≤ lamD D τ a - lamD D τ c := by
    intro a c hlt ha
    have hlt' : a.val < c.val := hlt
    have hc := c.isLt
    have ha1 : a.val + 1 < 2 * D.R.rS + D.R.k + 1 := by omega
    have e1 : lamD D τ a = -bOne D τ (a.val + 2 - D.R.k) :=
      lam_b D τ a _ (by omega) (by omega)
    have e2 : lamD D τ ⟨a.val + 1, ha1⟩ = -bOne D τ (a.val + 2 - D.R.k + 1) :=
      lam_b D τ _ _ (by omega) (show a.val + 1 + 2 = D.R.k + (a.val + 2 - D.R.k + 1) by omega)
    have hmono : lamD D τ c ≤ lamD D τ ⟨a.val + 1, ha1⟩ :=
      hanti.antitone (Fin.le_iff_val_le_val.mpr (show a.val + 1 ≤ c.val by omega))
    have hn := hnode τ (a.val + 2 - D.R.k) (by omega) (by omega)
    linarith
  have hN19 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := pow_nonneg hN0 19
  have hC11 : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) (lamD D τ)
      ((D.R.r : ℝ) ^ 19) := by
    intro a c hac
    by_cases ha : a.val < D.R.k - 1
    · by_cases hc : c.val < D.R.k - 1
      · exfalso
        apply hac
        unfold PI.BesselPeriodGGP.eps48
        rw [if_pos ha, if_pos hc]
      · have h1 := (hC6 a (by omega)).1
        have h2 := (hC7 c (by omega)).2
        have h0 := (hC6 ⟨0, by omega⟩ (show 0 + 1 < D.R.k by omega)).1
        have h0' := (hC6 ⟨0, by omega⟩ (show 0 + 1 < D.R.k by omega)).2
        rw [abs_of_nonneg (by linarith)]
        linarith
    · by_cases hc : c.val < D.R.k - 1
      · have h1 := (hC6 c (by omega)).1
        have h2 := (hC7 a (by omega)).2
        have h0 := (hC6 ⟨0, by omega⟩ (show 0 + 1 < D.R.k by omega)).1
        have h0' := (hC6 ⟨0, by omega⟩ (show 0 + 1 < D.R.k by omega)).2
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have hne : a ≠ c := by
          rintro rfl
          exact hac rfl
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have key := hnodeGap a c hlt ha
          rw [abs_of_nonneg (by linarith)]
          linarith
        · have key := hnodeGap c a hlt hc
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
  have hC13 : 100 * (((D.R.k * D.R.m ^ 5 : ℕ) : ℝ) + 1) ≤ (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by
    push_cast
    have hP : (1000 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
      have : (D.R.m : ℝ) ^ 1 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
      rw [pow_one] at this
      linarith
    have hKP : 1 ≤ (D.R.k : ℝ) * (D.R.m : ℝ) ^ 5 :=
      one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have hKP0 : 0 ≤ (D.R.k : ℝ) * (D.R.m : ℝ) ^ 5 := by linarith
    calc 100 * ((D.R.k : ℝ) * (D.R.m : ℝ) ^ 5 + 1) ≤ ((D.R.k : ℝ) * (D.R.m : ℝ) ^ 5) * 200 := by
          linarith
      _ ≤ ((D.R.k : ℝ) * (D.R.m : ℝ) ^ 5) * (D.R.m : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_left (by linarith) hKP0
      _ ≤ ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 5) * (D.R.m : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKN (by positivity)) (by positivity)
      _ = (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by ring
  have hC14 : 100 * (((D.R.k * D.R.m ^ 5 : ℕ) : ℝ) + 1) ≤ (D.R.r : ℝ) ^ 19 := by
    push_cast
    have h1 : (D.R.k : ℝ) * (D.R.m : ℝ) ^ 5 ≤ (D.R.r : ℝ) ^ 6 := by
      calc (D.R.k : ℝ) * (D.R.m : ℝ) ^ 5 ≤ (D.R.r : ℝ) * (D.R.r : ℝ) ^ 5 :=
            mul_le_mul hKN (by gcongr) (by positivity) hN0
        _ = (D.R.r : ℝ) ^ 6 := by ring
    have h13 : (200 : ℝ) ≤ (D.R.r : ℝ) ^ 13 := by
      calc (200 : ℝ) ≤ 1000 ^ 13 := by norm_num
        _ ≤ (D.R.r : ℝ) ^ 13 := by gcongr
    have h2 : 200 * (D.R.r : ℝ) ^ 6 ≤ (D.R.r : ℝ) ^ 19 := by
      calc 200 * (D.R.r : ℝ) ^ 6 ≤ (D.R.r : ℝ) ^ 13 * (D.R.r : ℝ) ^ 6 :=
            mul_le_mul_of_nonneg_right h13 (by positivity)
        _ = (D.R.r : ℝ) ^ 19 := by ring
    have h3 : (1 : ℝ) ≤ (D.R.r : ℝ) ^ 6 := one_le_pow₀ (by linarith)
    linarith
  have hGO := gapOK D.R.k D.R.rS (D.R.r : ℝ) hNeq (by omega) hN1000
  refine ⟨⟨by omega, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hGO.1, hC13, hC14, hC15⟩,
    hGO.2, ?_⟩
  funext i
  rfl

end GlobalTheory.SizeNum
