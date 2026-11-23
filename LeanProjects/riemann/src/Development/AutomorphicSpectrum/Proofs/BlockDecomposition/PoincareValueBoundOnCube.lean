import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ENNReal
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobCube

theorem norm_sq_left_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {ε : ℝ} (hε : 0 < ε) (h h' : ℝ → V)
    (hd : ∀ s ∈ Set.Icc (0 : ℝ) ε, HasDerivAt h (h' s) s)
    (hc : ContinuousOn h' (Set.Icc 0 ε)) :
    ‖h 0‖ ^ 2 ≤ (2 / ε) * (∫ s in Set.Icc (0 : ℝ) ε, ‖h s‖ ^ 2)
      + (2 * ε) * ∫ s in Set.Icc (0 : ℝ) ε, ‖h' s‖ ^ 2 := by
  have hε' : (0 : ℝ) ≤ ε := hε.le
  have hu : Set.uIcc (0 : ℝ) ε = Set.Icc 0 ε := Set.uIcc_of_le hε'
  have hcu : ContinuousOn (fun s => ‖h' s‖) (Set.uIcc (0 : ℝ) ε) := by
    rw [hu]; exact hc.norm
  have hhc : ContinuousOn h (Set.Icc 0 ε) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  set A : ℝ := ∫ s in (0 : ℝ)..ε, ‖h' s‖ with hA
  set B : ℝ := ∫ s in (0 : ℝ)..ε, ‖h' s‖ ^ 2 with hB
  have hAnn : 0 ≤ A := intervalIntegral.integral_nonneg hε' (fun _ _ => norm_nonneg _)

  have step1 : ∀ s ∈ Set.Icc (0 : ℝ) ε, ‖h 0‖ ≤ ‖h s‖ + A := by
    intro s hs
    have hsub : Set.uIcc (0 : ℝ) s ⊆ Set.Icc 0 ε := by
      rw [Set.uIcc_of_le hs.1]; exact Set.Icc_subset_Icc le_rfl hs.2
    have hint : IntervalIntegrable h' volume 0 s := (hc.mono hsub).intervalIntegrable
    have hftc : ∫ y in (0 : ℝ)..s, h' y = h s - h 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hd y (hsub hy)) hint
    have h1 : ‖h s - h 0‖ ≤ ∫ y in (0 : ℝ)..s, ‖h' y‖ := by
      rw [← hftc]; exact intervalIntegral.norm_integral_le_integral_norm hs.1
    have h2 : ∫ y in (0 : ℝ)..s, ‖h' y‖ ≤ A :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) hcu.intervalIntegrable
    have h3 : ‖h 0‖ ≤ ‖h s‖ + ‖h s - h 0‖ := by
      have := norm_sub_le (h s) (h s - h 0)
      simpa using this
    linarith

  have step2 : A ^ 2 ≤ ε * B := by
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..ε, (‖h' s‖ - A / ε) ^ 2 :=
      intervalIntegral.integral_nonneg hε' (fun _ _ => sq_nonneg _)
    have hi1 : IntervalIntegrable (fun s => ‖h' s‖ ^ 2) volume 0 ε :=
      (hcu.pow 2).intervalIntegrable
    have hi2 : IntervalIntegrable (fun s => ‖h' s‖) volume 0 ε := hcu.intervalIntegrable
    have hexp : ∫ s in (0 : ℝ)..ε, (‖h' s‖ - A / ε) ^ 2 = B - 2 * (A / ε) * A + (A / ε) ^ 2 * ε := by
      have : ∀ s, (‖h' s‖ - A / ε) ^ 2 = ‖h' s‖ ^ 2 - 2 * (A / ε) * ‖h' s‖ + (A / ε) ^ 2 := by
        intro s; ring
      simp_rw [this]
      rw [intervalIntegral.integral_add (hi1.sub (hi2.const_mul _)) (by simp),
        intervalIntegral.integral_sub hi1 (hi2.const_mul _),
        intervalIntegral.integral_const_mul]
      simp [hA, hB]
      ring
    rw [hexp] at hnn
    have h4 : B - 2 * (A / ε) * A + (A / ε) ^ 2 * ε = B - A ^ 2 / ε := by
      field_simp
      ring
    rw [h4] at hnn
    have h5 : A ^ 2 / ε ≤ B := by linarith
    rw [div_le_iff₀ hε] at h5
    linarith

  have hi3 : IntervalIntegrable (fun s => ‖h s‖ ^ 2) volume 0 ε := by
    have : ContinuousOn (fun s => ‖h s‖ ^ 2) (Set.uIcc (0 : ℝ) ε) := by
      rw [hu]; exact hhc.norm.pow 2
    exact this.intervalIntegrable
  have step3 : ε * ‖h 0‖ ^ 2 ≤ 2 * (∫ s in (0 : ℝ)..ε, ‖h s‖ ^ 2) + ε * (2 * A ^ 2) := by
    have hmono : ∫ _s in (0 : ℝ)..ε, ‖h 0‖ ^ 2 ≤ ∫ s in (0 : ℝ)..ε, (2 * ‖h s‖ ^ 2 + 2 * A ^ 2) := by
      refine intervalIntegral.integral_mono_on hε' (by simp)
        ((hi3.const_mul 2).add (by simp)) ?_
      intro s hs
      have h6 := step1 s hs
      have h7 : ‖h 0‖ ^ 2 ≤ (‖h s‖ + A) ^ 2 := by gcongr
      nlinarith [sq_nonneg (‖h s‖ - A)]
    rw [intervalIntegral.integral_add (hi3.const_mul 2) (by simp),
      intervalIntegral.integral_const_mul] at hmono
    simp at hmono
    linarith
  have conv : ∀ f : ℝ → ℝ, ∫ s in Set.Icc (0 : ℝ) ε, f s = ∫ s in (0 : ℝ)..ε, f s := by
    intro f
    rw [intervalIntegral.integral_of_le hε', integral_Icc_eq_integral_Ioc]
  rw [conv, conv, ← hB]
  have h8 : ‖h 0‖ ^ 2 ≤ (2 * (∫ s in (0 : ℝ)..ε, ‖h s‖ ^ 2) + ε * (2 * A ^ 2)) / ε := by
    rw [le_div_iff₀ hε]; linarith
  have h9 : (2 * (∫ s in (0 : ℝ)..ε, ‖h s‖ ^ 2) + ε * (2 * A ^ 2)) / ε
      = 2 / ε * (∫ s in (0 : ℝ)..ε, ‖h s‖ ^ 2) + 2 * A ^ 2 := by
    field_simp
  nlinarith

def Tl {ι : Type} [DecidableEq ι] (l : List ι) : Finset (List ι) :=
  l.foldr (fun i T => T ∪ T.image (fun M => M ++ [i])) {[]}

theorem Tl_nil {ι : Type} [DecidableEq ι] : Tl ([] : List ι) = {[]} := rfl

theorem Tl_cons {ι : Type} [DecidableEq ι] (i : ι) (l : List ι) :
    Tl (i :: l) = Tl l ∪ (Tl l).image (fun M => M ++ [i]) := rfl

theorem marg_bound {ι : Type} [Fintype ι] [DecidableEq ι] (ε : ℝ) (c : ℝ≥0∞)
    (Gf : List ι → (ι → ℝ) → ℝ≥0∞) (hm : ∀ L, Measurable (Gf L))
    (K : Set (ι → ℝ))
    (hK : ∀ x ∈ K, ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) ε, Function.update x i s ∈ K)
    (H : ∀ (L : List ι) (i : ι) (x : ι → ℝ), x ∈ K → x i = 0 →
      Gf L x ≤ c * (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf L (Function.update x i s))
        + c * ∫⁻ s in Set.Icc (0 : ℝ) ε, Gf (i :: L) (Function.update x i s))
    (l : List ι) (hl : l.Nodup) :
    ∀ (L : List ι) (x : ι → ℝ), x ∈ K → (∀ i ∈ l, x i = 0) →
      Gf L x ≤ (2 * c) ^ l.length * ∑ M ∈ Tl l,
        (∫⋯∫⁻_l.toFinset, Gf (M ++ L) ∂(fun _ : ι => (volume : Measure ℝ).restrict (Set.Icc 0 ε))) x := by
  induction l with
  | nil =>
    intro L x _ _
    simp [Tl_nil]
  | cons i l ih =>
    intro L x hx hz
    have hil : i ∉ l := (List.nodup_cons.mp hl).1
    have ih' := ih (List.nodup_cons.mp hl).2
    have hiS : i ∉ l.toFinset := by simpa using hil
    set μ : ι → Measure ℝ := fun _ : ι => (volume : Measure ℝ).restrict (Set.Icc 0 ε) with hμ
    set D : ℝ≥0∞ := (2 * c) ^ l.length with hD
    set Q : List ι → ℝ≥0∞ := fun N => (∫⋯∫⁻_insert i l.toFinset, Gf N ∂μ) x with hQ
    have key : ∀ N₀ : List ι,
        (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf N₀ (Function.update x i s)) ≤ D * ∑ M ∈ Tl l, Q (M ++ N₀) := by
      intro N₀
      have hmeas : ∀ M : List ι, Measurable fun s : ℝ =>
          (∫⋯∫⁻_l.toFinset, Gf (M ++ N₀) ∂μ) (Function.update x i s) := fun M =>
        ((hm _).lmarginal μ).comp (measurable_update x)
      calc (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf N₀ (Function.update x i s))
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) ε, D * ∑ M ∈ Tl l,
              (∫⋯∫⁻_l.toFinset, Gf (M ++ N₀) ∂μ) (Function.update x i s) := by
            refine setLIntegral_mono' measurableSet_Icc ?_
            intro s hs
            refine ih' N₀ _ (hK x hx i s hs) ?_
            intro j hj
            have hji : j ≠ i := fun e => hil (e ▸ hj)
            rw [Function.update_of_ne hji]
            exact hz j (List.mem_cons_of_mem _ hj)
        _ = D * ∑ M ∈ Tl l, Q (M ++ N₀) := by
            rw [lintegral_const_mul _ (Finset.measurable_sum _ fun M _ => hmeas M),
              lintegral_finsetSum _ fun M _ => hmeas M]
            congr 1
            refine Finset.sum_congr rfl fun M _ => ?_
            simp only [hQ]
            rw [lmarginal_insert _ (hm _) hiS]
    have hsum1 : ∑ M ∈ Tl l, Q (M ++ L) ≤ ∑ N ∈ Tl (i :: l), Q (N ++ L) := by
      refine Finset.sum_le_sum_of_subset ?_
      intro M hM
      simp only [Tl_cons, Finset.mem_union]
      exact Or.inl hM
    have hsum2 : ∑ M ∈ Tl l, Q (M ++ i :: L) ≤ ∑ N ∈ Tl (i :: l), Q (N ++ L) := by
      have hinj : Set.InjOn (fun M : List ι => M ++ [i]) (Tl l : Set (List ι)) :=
        fun a _ b _ hab => List.append_cancel_right hab
      have himg : ∑ M ∈ Tl l, Q (M ++ i :: L) = ∑ N ∈ (Tl l).image (fun M => M ++ [i]), Q (N ++ L) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun M _ => ?_
        simp
      rw [himg]
      refine Finset.sum_le_sum_of_subset ?_
      intro M hM
      simp only [Tl_cons, Finset.mem_union]
      exact Or.inr hM
    have hx0 : x i = 0 := hz i List.mem_cons_self
    calc Gf L x ≤ c * (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf L (Function.update x i s))
          + c * ∫⁻ s in Set.Icc (0 : ℝ) ε, Gf (i :: L) (Function.update x i s) := H L i x hx hx0
      _ ≤ c * (D * ∑ N ∈ Tl (i :: l), Q (N ++ L)) + c * (D * ∑ N ∈ Tl (i :: l), Q (N ++ L)) := by
          gcongr
          · exact (key L).trans (by gcongr)
          · exact (key (i :: L)).trans (by gcongr)
      _ = (2 * c) ^ (i :: l).length * ∑ N ∈ Tl (i :: l), Q (N ++ L) := by
          simp only [List.length_cons, pow_succ, hD]
          ring
      _ = _ := by
          simp only [hQ, List.toFinset_cons]

theorem contDiffOn_pd {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {U : Set (ι → ℝ)} {F : (ι → ℝ) → V} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (L : List ι) : ContDiffOn ℝ ∞ (pd L F) U := by
  induction L with
  | nil => simpa [pd_nil] using hF
  | cons i L ih =>
    rw [pd_cons]
    have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (pd L F)) U := ih.fderiv_of_isOpen hU (by simp)
    exact h1.clm_apply contDiffOn_const

theorem update_mem_cube {ι : Type} [DecidableEq ι] {ε : ℝ} {x : ι → ℝ}
    (hx : x ∈ Set.Icc (0 : ι → ℝ) (fun _ => ε)) (i : ι) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) ε) :
    Function.update x i s ∈ Set.Icc (0 : ι → ℝ) (fun _ => ε) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst h; simpa using hs.1
    · simpa [Function.update_of_ne h] using hx.1 j
  · intro j
    by_cases h : j = i
    · subst h; simpa using hs.2
    · simpa [Function.update_of_ne h] using hx.2 j

theorem line_bound {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {ε : ℝ} (hε : 0 < ε) {U : Set (ι → ℝ)} {F : (ι → ℝ) → V}
    (hU : IsOpen U) (hKU : Set.Icc (0 : ι → ℝ) (fun _ => ε) ⊆ U) (hF : ContDiffOn ℝ ∞ F U)
    (L : List ι) (i : ι) (x : ι → ℝ) (hx : x ∈ Set.Icc (0 : ι → ℝ) (fun _ => ε)) (hxi : x i = 0) :
    ‖pd L F x‖ ^ 2 ≤ (2 / ε) * (∫ s in Set.Icc (0 : ℝ) ε, ‖pd L F (Function.update x i s)‖ ^ 2)
      + (2 * ε) * ∫ s in Set.Icc (0 : ℝ) ε, ‖pd (i :: L) F (Function.update x i s)‖ ^ 2 := by
  have hup : ∀ s ∈ Set.Icc (0 : ℝ) ε, Function.update x i s ∈ U := fun s hs =>
    hKU (update_mem_cube hx i hs)
  have h0 : Function.update x i 0 = x := by
    rw [← hxi]; exact Function.update_eq_self i x
  have hcu : Continuous fun s : ℝ => Function.update x i s :=
    continuous_const.update i continuous_id
  have key := norm_sq_left_le hε (fun s => pd L F (Function.update x i s))
    (fun s => pd (i :: L) F (Function.update x i s)) ?_ ?_
  · simpa only [h0] using key
  · intro s hs
    have hdiff : DifferentiableAt ℝ (pd L F) (Function.update x i s) :=
      ((contDiffOn_pd hU hF L).contDiffAt (hU.mem_nhds (hup s hs))).differentiableAt (by simp)
    have := hdiff.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_update x i s)
    show HasDerivAt _ (fderiv ℝ (pd L F) (Function.update x i s) (Pi.single i 1)) s
    exact this
  · exact (contDiffOn_pd hU hF (i :: L)).continuousOn.comp hcu.continuousOn hup

theorem sobolev_cube : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℝ), 0 < ε →
    ∃ (T : Finset (List ι)) (C : ℝ), 0 ≤ C ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (U : Set (ι → ℝ)) (F : (ι → ℝ) → V), IsOpen U → Set.Icc (0 : ι → ℝ) (fun _ => ε) ⊆ U → ContDiffOn ℝ ∞ F U →
        ‖F 0‖ ^ 2 ≤ C * ∑ L ∈ T, ∫ t in Set.Icc (0 : ι → ℝ) (fun _ => ε), ‖pd L F t‖ ^ 2 := by
  intro ι _ _ ε hε
  have hc0 : 0 ≤ 2 / ε + 2 * ε := by positivity
  refine ⟨Tl (Finset.univ : Finset ι).toList,
    (2 * (2 / ε + 2 * ε)) ^ (Finset.univ : Finset ι).toList.length, by positivity, ?_⟩
  intro V _ _ _ U F hU hKU hF
  set c0 : ℝ := 2 / ε + 2 * ε with hc0def
  set K : Set (ι → ℝ) := Set.Icc (0 : ι → ℝ) (fun _ => ε) with hKdef
  have hKm : MeasurableSet K := measurableSet_Icc
  have hKc : IsCompact K := isCompact_Icc
  have hcont : ∀ L, ContinuousOn (pd L F) K := fun L =>
    (contDiffOn_pd hU hF L).continuousOn.mono hKU
  set Gf : List ι → (ι → ℝ) → ℝ≥0∞ :=
    fun L => K.indicator (fun t => ENNReal.ofReal (‖pd L F t‖ ^ 2)) with hGf
  have hm : ∀ L, Measurable (Gf L) := by
    intro L
    classical
    have h1 : ContinuousOn (fun t => ENNReal.ofReal (‖pd L F t‖ ^ 2)) K :=
      ENNReal.continuous_ofReal.comp_continuousOn ((hcont L).norm.pow 2)
    have h2 := h1.measurable_piecewise (continuousOn_const (c := (0 : ℝ≥0∞))) hKm
    have h3 : (fun _ : ι → ℝ => (0 : ℝ≥0∞)) = 0 := rfl
    rw [h3, Set.piecewise_eq_indicator] at h2
    exact h2
  have H : ∀ (L : List ι) (i : ι) (x : ι → ℝ), x ∈ K → x i = 0 →
      Gf L x ≤ ENNReal.ofReal c0 * (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf L (Function.update x i s))
        + ENNReal.ofReal c0 * ∫⁻ s in Set.Icc (0 : ℝ) ε, Gf (i :: L) (Function.update x i s) := by
    intro L i x hx hxi
    have h1 := line_bound hε hU hKU hF L i x hx hxi
    have hcu : Continuous fun s : ℝ => Function.update x i s :=
      continuous_const.update i continuous_id
    have hA : ∀ N, ContinuousOn (fun s => ‖pd N F (Function.update x i s)‖ ^ 2) (Set.Icc (0 : ℝ) ε) :=
      fun N => (((hcont N).comp hcu.continuousOn fun s hs => update_mem_cube hx i hs).norm).pow 2
    have hconv : ∀ N, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) ε, ‖pd N F (Function.update x i s)‖ ^ 2)
        = ∫⁻ s in Set.Icc (0 : ℝ) ε, Gf N (Function.update x i s) := by
      intro N
      rw [ofReal_integral_eq_lintegral_ofReal ((hA N).integrableOn_compact isCompact_Icc)
        (Filter.Eventually.of_forall fun _ => by positivity)]
      refine setLIntegral_congr_fun measurableSet_Icc ?_
      intro s hs
      simp only [hGf]
      rw [Set.indicator_of_mem (update_mem_cube hx i hs)]
    have hGx : Gf L x = ENNReal.ofReal (‖pd L F x‖ ^ 2) := by
      simp only [hGf]
      rw [Set.indicator_of_mem hx]
    have hAnn : ∀ N, 0 ≤ ∫ s in Set.Icc (0 : ℝ) ε, ‖pd N F (Function.update x i s)‖ ^ 2 :=
      fun N => integral_nonneg fun _ => by positivity
    rw [hGx, ← hconv, ← hconv]
    calc ENNReal.ofReal (‖pd L F x‖ ^ 2)
        ≤ ENNReal.ofReal ((2 / ε) * (∫ s in Set.Icc (0 : ℝ) ε, ‖pd L F (Function.update x i s)‖ ^ 2)
          + (2 * ε) * ∫ s in Set.Icc (0 : ℝ) ε, ‖pd (i :: L) F (Function.update x i s)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ ≤ ENNReal.ofReal (c0 * (∫ s in Set.Icc (0 : ℝ) ε, ‖pd L F (Function.update x i s)‖ ^ 2)
          + c0 * ∫ s in Set.Icc (0 : ℝ) ε, ‖pd (i :: L) F (Function.update x i s)‖ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e1 : 2 / ε ≤ c0 := by simp only [hc0def]; have : 0 < 2 * ε := by positivity
                                     linarith
          have e2 : 2 * ε ≤ c0 := by simp only [hc0def]; have : 0 < 2 / ε := by positivity
                                     linarith
          have := mul_le_mul_of_nonneg_right e1 (hAnn L)
          have := mul_le_mul_of_nonneg_right e2 (hAnn (i :: L))
          linarith
      _ = _ := by
          rw [ENNReal.ofReal_add (mul_nonneg hc0 (hAnn _)) (mul_nonneg hc0 (hAnn _)),
            ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hc0]
  have hb := marg_bound ε (ENNReal.ofReal c0) Gf hm K
    (fun x hx i s hs => update_mem_cube hx i hs) H (Finset.univ : Finset ι).toList
    (Finset.nodup_toList _) [] 0 ⟨le_rfl, fun _ => hε.le⟩ (by simp)
  have hpi : Measure.pi (fun _ : ι => (volume : Measure ℝ).restrict (Set.Icc 0 ε))
      = (volume : Measure (ι → ℝ)).restrict K := by
    have hK' : K = Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) ε) :=
      (Set.pi_univ_Icc (0 : ι → ℝ) (fun _ => ε)).symm
    rw [hK', volume_pi, Measure.restrict_pi_pi]
  have hnn : ∀ M : List ι, 0 ≤ ∫ t in K, ‖pd M F t‖ ^ 2 :=
    fun M => integral_nonneg fun _ => by positivity
  have hmarg : ∀ M : List ι,
      (∫⋯∫⁻_(Finset.univ : Finset ι).toList.toFinset, Gf (M ++ [])
        ∂(fun _ : ι => (volume : Measure ℝ).restrict (Set.Icc 0 ε))) 0
      = ENNReal.ofReal (∫ t in K, ‖pd M F t‖ ^ 2) := by
    intro M
    have hint : IntegrableOn (fun t => ‖pd M F t‖ ^ 2) K :=
      (((hcont M).norm).pow 2).integrableOn_compact hKc
    rw [Finset.toList_toFinset, ← lintegral_eq_lmarginal_univ, hpi, List.append_nil,
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun _ => by positivity)]
    simp only [hGf]
    rw [lintegral_indicator hKm, Measure.restrict_restrict hKm, Set.inter_self]
  have hG0 : Gf [] 0 = ENNReal.ofReal (‖F 0‖ ^ 2) := by
    simp only [hGf]
    rw [Set.indicator_of_mem (show (0 : ι → ℝ) ∈ K from ⟨le_rfl, fun _ => hε.le⟩), pd_nil]
  simp_rw [hmarg] at hb
  rw [hG0, ← ENNReal.ofReal_sum_of_nonneg (fun M _ => hnn M)] at hb
  have h2c : (2 * ENNReal.ofReal c0) ^ (Finset.univ : Finset ι).toList.length
      = ENNReal.ofReal ((2 * c0) ^ (Finset.univ : Finset ι).toList.length) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [h2c, ← ENNReal.ofReal_mul (by positivity)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun M _ => hnn M))).mp hb

end GlobalTheory.CompanionTheory.SobCube
