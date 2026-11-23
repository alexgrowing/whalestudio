import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace subgroupData

def qv (c : Fin 3 → ℂ) (t : ℝ) : ℂ := c 0 + c 1 * t + c 2 * t ^ 2

lemma qv_cont (c : Fin 3 → ℂ) : Continuous (qv c) := by
  unfold qv; fun_prop

lemma term_bd {z : ℂ} {w d la W D : ℝ} (hz : ‖z‖ ≤ la) (hw : |w| ≤ W) (hD : 0 < D) (hd : D ≤ |d|) :
    ‖z * (w : ℂ) / (d : ℂ)‖ ≤ la * W / D := by
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  rw [div_le_div_iff₀ (by linarith) hD]
  have hla : 0 ≤ la := (norm_nonneg _).trans hz
  exact mul_le_mul (mul_le_mul hz hw (abs_nonneg _) hla) hd hD.le (by positivity)

lemma lagrange (c : Fin 3 → ℂ) {t1 t2 t3 g la : ℝ} (hg : 0 < g) (h1 : 1 ≤ t1) (h3 : t3 ≤ 2)
    (h12 : g ≤ t2 - t1) (h23 : g ≤ t3 - t2)
    (p1 : ‖qv c t1‖ ≤ la) (p2 : ‖qv c t2‖ ≤ la) (p3 : ‖qv c t3‖ ≤ la) :
    ‖c‖ ≤ 12 * la / g ^ 2 := by
  have hla : 0 ≤ la := (norm_nonneg _).trans p1
  have d1 : g ^ 2 ≤ |(t1 - t2) * (t1 - t3)| := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have d2 : g ^ 2 ≤ |(t2 - t1) * (t2 - t3)| := by
    rw [abs_of_nonpos (by nlinarith)]; nlinarith
  have d3 : g ^ 2 ≤ |(t3 - t1) * (t3 - t2)| := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hg2 : 0 < g ^ 2 := by positivity
  have n1 : ((t1 - t2) * (t1 - t3) : ℂ) ≠ 0 := by
    have : (t1 - t2) * (t1 - t3) ≠ 0 := by intro h; rw [h, abs_zero] at d1; linarith
    exact_mod_cast this
  have n2 : ((t2 - t1) * (t2 - t3) : ℂ) ≠ 0 := by
    have : (t2 - t1) * (t2 - t3) ≠ 0 := by intro h; rw [h, abs_zero] at d2; linarith
    exact_mod_cast this
  have n3 : ((t3 - t1) * (t3 - t2) : ℂ) ≠ 0 := by
    have : (t3 - t1) * (t3 - t2) ≠ 0 := by intro h; rw [h, abs_zero] at d3; linarith
    exact_mod_cast this
  have a12 : (t1 : ℂ) - t2 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a13 : (t1 : ℂ) - t3 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a23 : (t2 : ℂ) - t3 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a21 : (t2 : ℂ) - t1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a31 : (t3 : ℂ) - t1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a32 : (t3 : ℂ) - t2 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have key : ∀ (w1 w2 w3 : ℝ), |w1| ≤ 4 → |w2| ≤ 4 → |w3| ≤ 4 →
      ‖qv c t1 * (w1 : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ) + qv c t2 * (w2 : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * (w3 : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ)‖ ≤ 12 * la / g ^ 2 := by
    intro w1 w2 w3 hw1 hw2 hw3
    refine (norm_add₃_le).trans ?_
    have := term_bd p1 hw1 hg2 d1
    have := term_bd p2 hw2 hg2 d2
    have := term_bd p3 hw3 hg2 d3
    have e : 12 * la / g ^ 2 = la * 4 / g ^ 2 + la * 4 / g ^ 2 + la * 4 / g ^ 2 := by ring
    linarith
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · have := key (t2 * t3) (t1 * t3) (t1 * t2) (by rw [abs_of_nonneg (by nlinarith)]; nlinarith)
      (by rw [abs_of_nonneg (by nlinarith)]; nlinarith) (by rw [abs_of_nonneg (by nlinarith)]; nlinarith)
    have e : c 0 = qv c t1 * ((t2 * t3 : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((t1 * t3 : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((t1 * t2 : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 0‖ ≤ _
    rw [e]; exact this
  · have := key (-(t2 + t3)) (-(t1 + t3)) (-(t1 + t2)) (by rw [abs_le]; constructor <;> nlinarith)
      (by rw [abs_le]; constructor <;> nlinarith) (by rw [abs_le]; constructor <;> nlinarith)
    have e : c 1 = qv c t1 * ((-(t2 + t3) : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((-(t1 + t3) : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((-(t1 + t2) : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 1‖ ≤ _
    rw [e]; exact this
  · have := key 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    have e : c 2 = qv c t1 * ((1 : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((1 : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((1 : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 2‖ ≤ _
    rw [e]; exact this

lemma E_closed (c : Fin 3 → ℂ) (la : ℝ) : IsClosed {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} :=
  isClosed_Icc.inter (isClosed_le (continuous_norm.comp (qv_cont c)) continuous_const)

lemma sublevel (c : Fin 3 → ℂ) {la g : ℝ} (hg : 0 < g)
    (hno : ∀ t1 t2 t3 : ℝ, 1 ≤ t1 → t3 ≤ 2 → g ≤ t2 - t1 → g ≤ t3 - t2 → ‖qv c t1‖ ≤ la →
      ‖qv c t2‖ ≤ la → ‖qv c t3‖ ≤ la → False) :
    volume {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} ≤ ENNReal.ofReal (2 * g) := by
  set E := {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} with hE
  have hcl : IsClosed E := E_closed c la
  have hbdd : BddBelow E := ⟨1, fun t ht => ht.1.1⟩
  rcases E.eq_empty_or_nonempty with h0 | hne
  · rw [h0, measure_empty]; exact bot_le
  set t1 := sInf E with ht1d
  have ht1 : t1 ∈ E := hcl.csInf_mem hne hbdd
  have hge1 : ∀ t ∈ E, t1 ≤ t := fun t ht => csInf_le hbdd ht
  set E2 := E ∩ Ici (t1 + g) with hE2
  rcases E2.eq_empty_or_nonempty with h2 | hne2
  · have hsub : E ⊆ Icc t1 (t1 + g) := by
      intro t ht
      refine ⟨hge1 t ht, ?_⟩
      by_contra hc
      have : t ∈ E2 := ⟨ht, le_of_lt (not_le.mp hc)⟩
      rw [h2] at this; exact this
    calc volume E ≤ volume (Icc t1 (t1 + g)) := measure_mono hsub
      _ = ENNReal.ofReal g := by rw [Real.volume_Icc]; ring_nf
      _ ≤ ENNReal.ofReal (2 * g) := ENNReal.ofReal_le_ofReal (by linarith)
  have hcl2 : IsClosed E2 := hcl.inter isClosed_Ici
  have hbdd2 : BddBelow E2 := ⟨1, fun t ht => ht.1.1.1⟩
  set t2 := sInf E2 with ht2d
  have ht2 : t2 ∈ E2 := hcl2.csInf_mem hne2 hbdd2
  have hge2 : ∀ t ∈ E2, t2 ≤ t := fun t ht => csInf_le hbdd2 ht
  have h12 : t1 + g ≤ t2 := Set.mem_Ici.mp ht2.2
  have hsub : E ⊆ Icc t1 (t1 + g) ∪ Icc t2 (t2 + g) := by
    intro t ht
    by_cases h : t < t1 + g
    · exact Or.inl ⟨hge1 t ht, h.le⟩
    · have htE2 : t ∈ E2 := ⟨ht, not_lt.mp h⟩
      refine Or.inr ⟨hge2 t htE2, ?_⟩
      by_contra hc
      exact hno t1 t2 t ht1.1.1 ht.1.2 (by linarith) (by linarith [not_le.mp hc]) ht1.2 ht2.1.2 ht.2
  calc volume E ≤ volume (Icc t1 (t1 + g) ∪ Icc t2 (t2 + g)) := measure_mono hsub
    _ ≤ volume (Icc t1 (t1 + g)) + volume (Icc t2 (t2 + g)) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * g) := by
        rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf

end subgroupData

open subgroupData in
theorem quadraticSublevelDecay' : SUB := by
  intro δ hδ0 hδ1
  refine ⟨22, ?_⟩
  intro c
  set M := ‖c‖ with hMd
  have hM0 : 0 ≤ M := norm_nonneg _
  have hint : ∀ t : ℝ, (1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ) ≤ 1 := fun t =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (c 0 + c 1 * t + c 2 * t ^ 2)])
      (by linarith)
  by_cases hM : M ≤ 1
  · calc (∫⁻ t in Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)))
        ≤ ∫⁻ t in Icc (1:ℝ) 2, 1 :=
          setLIntegral_mono' measurableSet_Icc (fun t _ => ENNReal.ofReal_le_one.mpr (hint t))
      _ = 1 := by rw [setLIntegral_const, Real.volume_Icc]; norm_num
      _ ≤ ENNReal.ofReal (22 * (1 + M) ^ (-δ / 2)) := by
          rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
          have : (2:ℝ) ^ (-1:ℝ) ≤ (1 + M) ^ (-δ / 2) := by
            calc (2:ℝ) ^ (-1:ℝ) ≤ 2 ^ (-δ / 2) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ ≤ (1 + M) ^ (-δ / 2) := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
          have h2 : (2:ℝ) ^ (-1:ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
          linarith
  push Not at hM
  set s := M ^ ((1:ℝ) / 4) with hs
  have hs0 : 0 < s := by positivity
  have hs4 : s ^ 4 = M := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hs1 : 1 < s := by
    by_contra h; push Not at h
    have : s ^ 4 ≤ 1 := pow_le_one₀ hs0.le h
    linarith
  set E := {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ s ^ 2} with hE
  have hvol : volume E ≤ ENNReal.ofReal (2 * (5 / s)) := by
    apply sublevel c (by positivity)
    intro t1 t2 t3 h1 h3 h12 h23 p1 p2 p3
    have hl := lagrange c (by positivity) h1 h3 h12 h23 p1 p2 p3
    have e : 12 * s ^ 2 / (5 / s) ^ 2 = 12 * s ^ 4 / 25 := by field_simp; ring
    rw [e, hs4] at hl
    linarith
  have hEm : MeasurableSet E := (E_closed c _).measurableSet
  set K := (1 + s ^ 2) ^ (-δ) with hK
  have pw : ∀ t ∈ Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) ≤
      E.indicator 1 t + ENNReal.ofReal K := by
    intro t ht
    by_cases hp : ‖qv c t‖ ≤ s ^ 2
    · have htE : t ∈ E := ⟨ht, hp⟩
      rw [indicator_of_mem htE]
      exact le_trans (ENNReal.ofReal_le_one.mpr (hint t)) le_self_add
    · refine le_trans ?_ le_add_self
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by
        have : s ^ 2 < ‖qv c t‖ := not_le.mp hp
        simp only [qv] at this; linarith) (by linarith)
  have hfin : 2 * (5 / s) + K ≤ 22 * (1 + M) ^ (-δ / 2) := by
    have hA : K ≤ (1 + M) ^ (-δ / 2) := by
      have e : K = ((1 + s ^ 2) ^ 2) ^ (-δ / 2) := by
        rw [hK, ← Real.rpow_natCast (1 + s ^ 2) 2, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
      rw [e]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by rw [← hs4]; nlinarith) (by linarith)
    have hB : 1 / (2 * s) ≤ (1 + M) ^ (-δ / 2) := by
      calc 1 / (2 * s) ≤ (1 + s)⁻¹ := by
            rw [one_div]; exact inv_anti₀ (by positivity) (by linarith)
        _ = ((1 + s) ^ 4) ^ (-(1:ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_neg_one]; norm_num
        _ ≤ (1 + M) ^ (-(1:ℝ) / 4) := by
            apply Real.rpow_le_rpow_of_nonpos (by linarith) _ (by norm_num)
            rw [← hs4]; nlinarith [pow_pos hs0 3]
        _ ≤ (1 + M) ^ (-δ / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have e2 : 2 * (5 / s) = 20 * (1 / (2 * s)) := by field_simp; ring
    have hX : 0 ≤ (1 + M) ^ (-δ / 2) := by positivity
    rw [e2]; linarith
  calc (∫⁻ t in Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)))
      ≤ ∫⁻ t in Icc (1:ℝ) 2, (E.indicator 1 t + ENNReal.ofReal K) := setLIntegral_mono' measurableSet_Icc pw
    _ = (∫⁻ t in Icc (1:ℝ) 2, E.indicator 1 t) + ∫⁻ _ in Icc (1:ℝ) 2, ENNReal.ofReal K :=
        lintegral_add_right _ measurable_const
    _ ≤ volume E + ENNReal.ofReal K := by
        gcongr
        · calc (∫⁻ t in Icc (1:ℝ) 2, E.indicator 1 t) ≤ ∫⁻ t, E.indicator 1 t := setLIntegral_le_lintegral _ _
            _ = volume E := lintegral_indicator_one hEm
        · rw [setLIntegral_const, Real.volume_Icc]; norm_num
    _ ≤ ENNReal.ofReal (2 * (5 / s)) + ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (2 * (5 / s) + K) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (22 * (1 + M) ^ (-δ / 2)) := ENNReal.ofReal_le_ofReal hfin
end ReciprocityTheory.ChartRestriction.DS.Xi
