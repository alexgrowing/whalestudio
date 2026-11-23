import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open Finset

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

private lemma gl2b2_twoTors (e : ℕ) (he : 1 ≤ e) :
    (Finset.univ.filter (fun c : ZMod (2 ^ e) => c + c = 0)).card = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  have hn : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  have hpos : 0 < 2 ^ k := by positivity
  have hlt : 2 ^ k < 2 ^ (k + 1) := by omega
  have hne : (0 : ZMod (2 ^ (k + 1))) ≠ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
    intro h
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at h2
    omega
  have hset : Finset.univ.filter (fun c : ZMod (2 ^ (k + 1)) => c + c = 0) =
      {0, ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hc
      have hv := congrArg ZMod.val hc
      rw [ZMod.val_add, ZMod.val_zero] at hv
      have hcl := ZMod.val_lt c
      rw [← ZMod.natCast_zmod_val c]
      rcases Nat.lt_or_ge (c.val + c.val) (2 ^ (k + 1)) with h1 | h1
      · rw [Nat.mod_eq_of_lt h1] at hv
        left
        have : c.val = 0 := by omega
        rw [this, Nat.cast_zero]
      · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at hv
        right
        have : c.val = 2 ^ k := by omega
        rw [this]
    · rintro (rfl | rfl)
      · simp
      · rw [← Nat.cast_add, ← hn, ZMod.natCast_self]
  rw [hset, Finset.card_pair hne]

theorem real_character_count : Formalism.HermitianLattices.ZeroFreeRegionGL2.RealCharCount := by
  intro e he
  have : (Finset.univ.filter (fun g : ZMod 2 × ZMod 2 × ZMod (2 ^ e) => g + g = 0)) =
      (Finset.univ : Finset (ZMod 2)) ×ˢ ((Finset.univ : Finset (ZMod 2)) ×ˢ
        (Finset.univ.filter (fun c : ZMod (2 ^ e) => c + c = 0))) := by
    ext ⟨a, b, c⟩
    simp only [mem_filter, mem_univ, true_and, mem_product, Prod.mk_add_mk, Prod.mk_eq_zero]
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · intro h; exact ⟨CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero b, h⟩
  rw [this, Finset.card_product, Finset.card_product, gl2b2_twoTors e he]
  simp

theorem numerical_nonvanishing_bound : Formalism.HermitianLattices.ZeroFreeRegionGL2.SmoothingSizeBounds := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.SmoothingSizeBounds
  intro ε hε
  have hε' : ε ≠ 0 := ne_of_gt hε
  refine ⟨max 2 ((4:ℝ) ^ (3 / ε)), ?_⟩
  intro x hx y lam hy hlam hlamle
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hx4 : (4:ℝ) ^ (3 / ε) ≤ x := le_trans (le_max_right _ _) hx
  have ht4 : 4 ≤ x ^ (ε / 3) := by
    have h1 : ((4:ℝ) ^ (3 / ε)) ^ (ε / 3) ≤ x ^ (ε / 3) :=
      Real.rpow_le_rpow (by positivity) hx4 (by positivity)
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4)] at h1
    have h3 : 3 / ε * (ε / 3) = 1 := by field_simp <;> ring
    rw [h3, Real.rpow_one] at h1
    exact h1
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hLne : Real.log x ≠ 0 := ne_of_gt hL
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith
  have hly : x ^ (ε / 3) - Real.log 3 ≤ Real.log y := by
    rw [← Real.exp_le_exp, Real.exp_log hypos, Real.exp_sub,
      Real.exp_log (by norm_num : (0:ℝ) < 3)]
    exact hy
  have ha : x ^ (ε / 3) / 2 ≤ Real.log y := by linarith
  refine ⟨ha, ?_, ?_⟩
  · have hsplit : x ^ (ε / 3) = x ^ (2 * ε / 15) * x ^ (ε / 5) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [le_div_iff₀ hlam]
    calc x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) * lam
        ≤ x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) * (2 * x ^ (ε / 5) * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hlamle (by positivity)
      _ = x ^ (ε / 3) / 2 := by rw [hsplit]; field_simp <;> ring
      _ ≤ Real.log y := ha
  · have hsplit : x ^ (ε / 3) = x ^ (ε / 6) * x ^ (ε / 6) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hs : 0 ≤ x ^ (ε / 6) / 2 := by positivity
    calc x ^ (ε / 6) / 2 = Real.sqrt ((x ^ (ε / 6) / 2) ^ 2) := (Real.sqrt_sq hs).symm
      _ ≤ Real.sqrt (Real.log y) := by
          apply Real.sqrt_le_sqrt
          have h5 : (x ^ (ε / 6) / 2) ^ 2 = x ^ (ε / 3) / 4 := by rw [hsplit]; ring
          rw [h5]
          have : 0 ≤ x ^ (ε / 3) := by positivity
          linarith

private lemma gl2b2_intH (b : ℝ) (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-b * v ^ (39 / 100 : ℝ)))
      (Set.Ioi 0) := by
  exact integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb

private lemma gl2b2_ptw (c v lam : ℝ) (hc : 0 < c) (hv : 1 ≤ v) (hl0 : 0 < lam)
    (hl : lam ≤ v ^ (61 / 100 : ℝ)) :
    (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := by
  have hv0 : 0 < v := by linarith
  have h61 : v ^ (61 / 100 : ℝ) ≤ v := by
    calc v ^ (61 / 100 : ℝ) ≤ v ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
      _ = v := Real.rpow_one v
  have hlv : lam ≤ v := le_trans hl h61
  have hsq : Real.sqrt v ≤ v ^ (61 / 100 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
  have hsplit : v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ) = v := by
    rw [← Real.rpow_add hv0]; norm_num
  have hD : 0 < lam + Real.sqrt v := by positivity
  have h39 : 0 ≤ v ^ (39 / 100 : ℝ) := by positivity
  have hkey : v ^ (39 / 100 : ℝ) * (lam + Real.sqrt v) ≤ 2 * v := by
    nlinarith [mul_le_mul_of_nonneg_left hl h39, mul_le_mul_of_nonneg_left hsq h39]
  have hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_left hkey hc.le]
  have hpoly : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlv) hv0.le, mul_nonneg (sub_nonneg.mpr hlv) hl0.le]
  calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
      ≤ (4 * v ^ (2 : ℝ)) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) :=
        mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
    _ = 4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := by ring

private lemma gl2b2_big_lemma {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → M ≤ x ^ a := by
  refine ⟨max 1 (|M| ^ (1 / a)), le_max_left _ _, fun x hx => ?_⟩
  have h2 : |M| ^ (1 / a) ≤ x := le_trans (le_max_right _ _) hx
  have h3 : (|M| ^ (1 / a)) ^ a ≤ x ^ a :=
    Real.rpow_le_rpow (by positivity) h2 ha.le
  rw [← Real.rpow_mul (abs_nonneg M), one_div_mul_cancel ha.ne', Real.rpow_one] at h3
  exact le_trans (le_abs_self M) h3

theorem gl2b2_thinIntegral : Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral
  intro ε c hε hc
  set I : ℝ := ∫ v in Set.Ioi 0, v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) with hI
  have hIint := gl2b2_intH (c / 4) (by positivity)
  have hI0 : 0 ≤ I := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro v hv
    have : 0 < v := hv
    positivity
  set δ : ℝ := 13 * ε / 20000 with hδ
  set δ' : ℝ := 13 * ε / 40000 with hδ'
  have hδpos : 0 < δ := by positivity
  have hδ'pos : 0 < δ' := by positivity
  obtain ⟨X1, -, hX1'⟩ := gl2b2_big_lemma (a := ε / 300) (by positivity) 2
  obtain ⟨X2, -, hX2'⟩ := gl2b2_big_lemma (a := ε / 8) (by positivity) (32 * I / c)
  obtain ⟨X3, -, hX3'⟩ := gl2b2_big_lemma (a := δ) hδpos (2 / δ' ^ 2)
  refine ⟨c / 8, max (max X1 X2) (max X3 2), by positivity, ?_⟩
  intro x hx V lam hV hlam1 hlam
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : (2:ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hVx : x ^ (33 * ε / 100) ≤ V := by
    have h1 := hX1' x hx1
    have hs : x ^ (ε / 3) = x ^ (33 * ε / 100) * x ^ (ε / 300) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hpos : 0 ≤ x ^ (33 * ε / 100) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos]
  have hV1 : 1 ≤ V := le_trans (Real.one_le_rpow hxone (by positivity)) hVx
  have hV0 : 0 < V := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLle : Real.log x ≤ x ^ δ' / δ' := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 δ')
    rw [Real.log_rpow hx0] at h
    rw [le_div_iff₀ hδ'pos]
    linarith
  have hL2 : Real.log x ^ 2 ≤ x ^ δ / δ' ^ 2 := by
    have hsq : x ^ δ = x ^ δ' * x ^ δ' := by
      rw [← Real.rpow_add hx0]; congr 1; rw [hδ, hδ']; ring
    have h2 : Real.log x ^ 2 ≤ (x ^ δ' / δ') ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hLle) hL0.le,
        mul_nonneg (sub_nonneg.mpr hLle) (sub_nonneg.mpr hLle)]
    rw [hsq]
    calc Real.log x ^ 2 ≤ (x ^ δ' / δ') ^ 2 := h2
      _ = x ^ δ' * x ^ δ' / δ' ^ 2 := by ring
  have hlamV : lam ≤ V ^ (61 / 100 : ℝ) := by
    have h1 : (x ^ (33 * ε / 100)) ^ (61 / 100 : ℝ) ≤ V ^ (61 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hVx (by norm_num)
    rw [← Real.rpow_mul hx0.le] at h1
    have hs : x ^ (33 * ε / 100 * (61 / 100)) = x ^ (ε / 5) * x ^ δ * x ^ δ := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; rw [hδ]; ring
    rw [hs] at h1
    have h3 := hX3' x hx3
    have h4 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * (x ^ δ / δ' ^ 2) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    have h5 : 2 * x ^ (ε / 5) * (x ^ δ / δ' ^ 2) = x ^ (ε / 5) * x ^ δ * (2 / δ' ^ 2) := by ring
    have h6 : x ^ (ε / 5) * x ^ δ * (2 / δ' ^ 2) ≤ x ^ (ε / 5) * x ^ δ * x ^ δ :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hpt : ∀ v ∈ Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
        (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ))) := by
    intro v hv
    have hv' : V < v := hv
    have hv1 : 1 ≤ v := by linarith
    have hlv : lam ≤ v ^ (61 / 100 : ℝ) :=
      le_trans hlamV (Real.rpow_le_rpow hV0.le hv'.le (by norm_num))
    have h1 := gl2b2_ptw c v lam hc hv1 (by linarith) hlv
    have h39 : V ^ (39 / 100 : ℝ) ≤ v ^ (39 / 100 : ℝ) :=
      Real.rpow_le_rpow hV0.le hv'.le (by norm_num)
    have h2 : Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) ≤
        Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left h39 hc.le]
    have hv2 : 0 ≤ v ^ (2 : ℝ) := by positivity
    calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
        ≤ 4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := h1
      _ ≤ 4 * (v ^ (2 : ℝ) * (Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
            Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hv2) (by norm_num)
      _ = _ := by ring
  have hgint : MeasureTheory.IntegrableOn (fun v : ℝ => 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
      (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))) (Set.Ioi V) :=
    (hIint.mono_set (Set.Ioi_subset_Ioi hV0.le)).const_mul _
  have hFmeas : MeasureTheory.AEStronglyMeasurable
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))
      (MeasureTheory.volume.restrict (Set.Ioi V)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hFint : MeasureTheory.IntegrableOn
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) := by
    refine MeasureTheory.Integrable.mono' hgint hFmeas ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt v hv
  refine ⟨hFint, ?_⟩
  have hw : x ^ (ε / 8) ≤ V ^ (39 / 100 : ℝ) := by
    have h1 : (x ^ (33 * ε / 100)) ^ (39 / 100 : ℝ) ≤ V ^ (39 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hVx (by norm_num)
    rw [← Real.rpow_mul hx0.le] at h1
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hxone ?_) h1
    linarith
  have hInt_le : (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤
      4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I := by
    calc (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))
        ≤ ∫ v in Set.Ioi V, 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
            (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ))) :=
          MeasureTheory.setIntegral_mono_on hFint hgint measurableSet_Ioi hpt
      _ = 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
            ∫ v in Set.Ioi V, v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hI]
          apply MeasureTheory.setIntegral_mono_set hIint
          · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
            intro v hv
            have : 0 < v := hv
            show (0:ℝ) ≤ _
            positivity
          · exact (Set.Ioi_subset_Ioi hV0.le).eventuallyLE
  have hw2 : 32 * I / c ≤ x ^ (ε / 8) := hX2' x hx2
  have h4I : 4 * I ≤ Real.exp (c / 8 * x ^ (ε / 8)) := by
    have h1 := Real.add_one_le_exp (c / 8 * x ^ (ε / 8))
    have h2 : 4 * I ≤ c / 8 * x ^ (ε / 8) := by
      rw [div_le_iff₀ hc] at hw2
      linarith
    linarith
  have hE1 : Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) ≤ Real.exp (-(c / 4) * x ^ (ε / 8)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hw hc.le]
  have hsplitE : Real.exp (-(c / 4) * x ^ (ε / 8)) =
      (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ * Real.exp (-(c / 8) * x ^ (ε / 8)) := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  calc (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))
      ≤ 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I := hInt_le
    _ ≤ 4 * Real.exp (-(c / 4) * x ^ (ε / 8)) * I :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE1 (by norm_num)) hI0
    _ = (4 * I) * (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ * Real.exp (-(c / 8) * x ^ (ε / 8)) := by
        rw [hsplitE]; ring
    _ ≤ Real.exp (c / 8 * x ^ (ε / 8)) * (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ *
          Real.exp (-(c / 8) * x ^ (ε / 8)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4I (by positivity))
          (Real.exp_pos _).le
    _ = Real.exp (-(c / 8) * x ^ (ε / 8)) := by
        rw [mul_inv_cancel₀ (Real.exp_pos _).ne']; ring

theorem nonvanishing_of_hypothesis : Formalism.HermitianLattices.ZeroFreeRegionGL2.TailIntegralBoundOfPsiBound := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.TailIntegralBoundOfPsiBound
  intro ε c C hε hc hC
  obtain ⟨c0, X0, hc0, hX0⟩ := gl2b2_thinIntegral ε c hε hc
  obtain ⟨XN, hXN⟩ := numerical_nonvanishing_bound ε hε
  obtain ⟨XW, -, hXW⟩ := gl2b2_big_lemma (a := ε / 8) (by positivity) (2 * C / c0)
  refine ⟨c0 / 2, max (max X0 XN) XW, by positivity, ?_⟩
  intro x hx y lam psi0 hy hlam1 hlam hpsi
  have hxX0 : X0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxN : XN ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxW : XW ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hV, -, -⟩ := hXN x hxN y lam hy (by linarith) hlam
  obtain ⟨hGint, hGle⟩ := hX0 x hxX0 (Real.log y) lam hV hlam1 hlam
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy
  set G : ℝ → ℝ := fun v => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) with hGdef
  have himg : Real.log '' Set.Ioi y = Set.Ioi (Real.log y) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.log_lt_log hypos hu
    · intro hv
      refine ⟨Real.exp v, ?_, Real.log_exp v⟩
      have h1 : Real.exp (Real.log y) < Real.exp v := Real.exp_lt_exp.mpr hv
      rwa [Real.exp_log hypos] at h1
  have hderiv : ∀ u ∈ Set.Ioi y, HasDerivWithinAt Real.log u⁻¹ (Set.Ioi y) u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hypos hu
    exact (Real.hasDerivAt_log hu0.ne').hasDerivWithinAt
  have hinj : Set.InjOn Real.log (Set.Ioi y) :=
    Real.log_injOn_pos.mono (Set.Ioi_subset_Ioi hypos.le)
  have hHint : MeasureTheory.IntegrableOn (fun u : ℝ => |u⁻¹| • G (Real.log u)) (Set.Ioi y) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
      hinj G).mp (by rw [himg]; exact hGint)
  have hHeq : (∫ u in Set.Ioi y, |u⁻¹| • G (Real.log u)) = ∫ v in Set.Ioi (Real.log y), G v := by
    have h1 := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
      hinj G
    rw [himg] at h1
    exact h1.symm
  have hbound : ∀ u ∈ Set.Ioi y, ‖psi0 u / (u : ℂ) ^ 2‖ ≤ C * (|u⁻¹| • G (Real.log u)) := by
    intro u hu
    have hu0 : 0 < u := lt_trans hypos hu
    have hu0' : u ≠ 0 := hu0.ne'
    have h1 := hpsi u (le_of_lt hu)
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
      abs_of_pos (inv_pos.mpr hu0), smul_eq_mul, div_le_iff₀ (by positivity)]
    have hG : G (Real.log u) = (Real.log u + lam) ^ 2 *
        Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))) := rfl
    have hu2 : u⁻¹ * u ^ 2 = u := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hu0', one_mul]
    rw [hG]
    calc ‖psi0 u‖ ≤ C * u * (Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))) := h1
      _ = C * (u⁻¹ * ((Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))))) * u ^ 2 := by
        rw [show C * (u⁻¹ * ((Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))))) * u ^ 2 =
          C * ((Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) * (u⁻¹ * u ^ 2) by ring,
          hu2]
        ring
  have hnorm : ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤
      ∫ u in Set.Ioi y, C * (|u⁻¹| • G (Real.log u)) :=
    MeasureTheory.norm_integral_le_of_norm_le (hHint.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  rw [MeasureTheory.integral_const_mul, hHeq] at hnorm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
  refine mul_le_mul_of_nonneg_left ?_ hypos.le
  have hw := hXW x hxW
  have hCexp : C ≤ Real.exp (c0 / 2 * x ^ (ε / 8)) := by
    have h1 := Real.add_one_le_exp (c0 / 2 * x ^ (ε / 8))
    rw [div_le_iff₀ hc0] at hw
    linarith
  calc ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ C * ∫ v in Set.Ioi (Real.log y), G v := hnorm
    _ ≤ C * Real.exp (-c0 * x ^ (ε / 8)) := mul_le_mul_of_nonneg_left hGle hC.le
    _ ≤ Real.exp (c0 / 2 * x ^ (ε / 8)) * Real.exp (-c0 * x ^ (ε / 8)) :=
        mul_le_mul_of_nonneg_right hCexp (Real.exp_pos _).le
    _ = Real.exp (-(c0 / 2) * x ^ (ε / 8)) := by rw [← Real.exp_add]; congr 1; ring

theorem character_estimate_of_hypothesis : Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSmoothingEstimate := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSmoothingEstimate
  intro ε c C hε hc hC
  obtain ⟨c', x₀, hc', h⟩ := nonvanishing_of_hypothesis ε c C hε hc hC
  refine ⟨c', x₀, hc', ?_⟩
  intro x hx y lam hy h1 h2
  constructor
  · intro N _ χ hG hb
    rw [hG, norm_neg]
    exact h x hx y lam _ hy h1 h2 hb
  · intro hG hb
    rw [hG, abs_neg]
    have h3 := h x hx y lam (fun u => ((Chebyshev.psi u - u : ℝ) : ℂ)) hy h1 h2
      (by intro u hu; simp only [Complex.norm_real, Real.norm_eq_abs]; exact hb u hu)
    have hcast : ((y : ℂ) * ∫ u in Set.Ioi y, ((Chebyshev.psi u - u : ℝ) : ℂ) / (u : ℂ) ^ 2) =
        ((y * ∫ u in Set.Ioi y, (Chebyshev.psi u - u) / u ^ 2 : ℝ) : ℂ) := by
      have h4 : (∫ u in Set.Ioi y, ((Chebyshev.psi u - u : ℝ) : ℂ) / (u : ℂ) ^ 2) =
          ∫ u in Set.Ioi y, (((Chebyshev.psi u - u) / u ^ 2 : ℝ) : ℂ) := by
        congr 1
        ext u
        push_cast
        try ring
      rw [h4, Complex.ofReal_mul]
      congr 1
      first
        | exact MeasureTheory.integral_ofReal
        | exact integral_ofReal
        | exact integral_complex_ofReal
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at h3
    exact h3

end Formalism.HermitianLattices.ZeroFreeRegionGL2
