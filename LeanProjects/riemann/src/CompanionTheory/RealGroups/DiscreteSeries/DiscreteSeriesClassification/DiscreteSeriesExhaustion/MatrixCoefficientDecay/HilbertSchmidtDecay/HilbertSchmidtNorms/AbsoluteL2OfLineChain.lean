import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.LineCurve

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace CompanionTheory.RgExh.Dec.L.AB

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)} {m : ℕ}
    {A : Fin m → Matrix (Fin n) (Fin n) ℂ} {ν : ∀ j, Measure (PSub ε (A j))} {τ : Fin m → S7.UJ ε → ℝ}
    {r : Fin m → ℝ} {Z : Fin m → Finset ℂ} {M c₁ R₀ C : ℝ}

theorem far_real (a b C c₁ s w c'' r t τy τx : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hlow : C⁻¹ * Real.exp (2 * t) * b ≤ a) (hup : a ≤ C * Real.exp (2 * t) * b)
    (hlog : c₁ * Real.log a ≤ τy) (hτ : τy = τx + t) (hτx : τx < 1) (hc₁ : 0 < c₁)
    (hs : s ≤ 0) (hw1 : s ≤ w) (hw2 : w ≤ s + 2 * c₁ * c'') (hc0 : 0 < c'') :
    a ^ w * Real.exp (2 * r * t) ≤ (C ^ (-s) * Real.exp (2 * c'')) * b ^ s * Real.exp (2 * (r + s + c'') * t) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hC : 0 < C := by
    by_contra hC'
    have hC : C ≤ 0 := not_lt.mp hC'
    have : C * Real.exp (2 * t) * b ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le) hb0.le
    linarith
  have hloga : 0 ≤ Real.log a := Real.log_nonneg ha
  have hτy0 : 0 ≤ τy := le_trans (mul_nonneg hc₁.le hloga) hlog

  have h1 : a ^ (w - s) ≤ Real.exp (2 * c'' * (1 + t)) := by
    rw [Real.rpow_def_of_pos ha0]
    apply Real.exp_le_exp.mpr
    have hl : Real.log a ≤ τy / c₁ := by rw [le_div_iff₀ hc₁]; linarith
    calc Real.log a * (w - s) ≤ τy / c₁ * (w - s) := mul_le_mul_of_nonneg_right hl (by linarith)
      _ ≤ τy / c₁ * (2 * c₁ * c'') := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hτy0 hc₁.le)
      _ = 2 * c'' * τy := by field_simp
      _ ≤ 2 * c'' * (1 + t) := by apply mul_le_mul_of_nonneg_left _ (by linarith); linarith

  have h2 : a ^ s ≤ C ^ (-s) * Real.exp (2 * t * s) * b ^ s := by
    have hpos : 0 < C⁻¹ * Real.exp (2 * t) * b := by positivity
    calc a ^ s ≤ (C⁻¹ * Real.exp (2 * t) * b) ^ s := Real.rpow_le_rpow_of_nonpos hpos hlow hs
      _ = C ^ (-s) * Real.exp (2 * t * s) * b ^ s := by
        rw [Real.mul_rpow (by positivity) hb0.le, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
          Real.inv_rpow hC.le, Real.rpow_neg hC.le, ← Real.exp_mul]
  have hsplit : a ^ w = a ^ s * a ^ (w - s) := by
    rw [← Real.rpow_add ha0]; ring_nf
  rw [hsplit]
  calc a ^ s * a ^ (w - s) * Real.exp (2 * r * t)
      ≤ (C ^ (-s) * Real.exp (2 * t * s) * b ^ s) * Real.exp (2 * c'' * (1 + t)) * Real.exp (2 * r * t) := by
        gcongr
    _ = (C ^ (-s) * Real.exp (2 * c'')) * b ^ s * Real.exp (2 * (r + s + c'') * t) := by
        have : Real.exp (2 * t * s) * Real.exp (2 * c'' * (1 + t)) * Real.exp (2 * r * t) =
            Real.exp (2 * c'') * Real.exp (2 * (r + s + c'') * t) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
        calc C ^ (-s) * Real.exp (2 * t * s) * b ^ s * Real.exp (2 * c'' * (1 + t)) * Real.exp (2 * r * t)
            = C ^ (-s) * b ^ s * (Real.exp (2 * t * s) * Real.exp (2 * c'' * (1 + t)) * Real.exp (2 * r * t)) := by ring
          _ = _ := by rw [this]; ring

theorem far_est (hLC : LineChain) (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (hn : 0 < n) (s : ℝ) (hs : s ≤ 0) (hL : ∀ f ∈ S, LevelF ε f s)
    (c'' : ℝ) (hc0 : 0 < c'') (hc1 : c'' ≤ 1) (j : Fin m) (hz : ∀ z ∈ Z j, z.re ≠ -(r j + s + c''))
    (U : Set (S7.UJ ε)) (hUm : MeasurableSet U) (hUK : ∀ g (k : S7.KG ε), g ∈ U → g * (k : S7.UJ ε) ∈ U)
    (hUτ : ∀ x : PSub ε (A j), (x : S7.UJ ε) ∈ U → c₁ * Real.log (Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) ≤ τ j x)
    (R₂ : ℝ) (hR₂ : 1 ≤ R₂) (hR₂' : 1 ≤ c₁ * Real.log R₂) (w : ℝ) (hw1 : s ≤ w) (hw2 : w ≤ s + 2 * c₁ * c'')
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (hf : f ∈ S) :
    ∫⁻ g : S7.UJ ε, (U ∩ {g | R₂ < Formalism.REAL.hs (S7.toM g)}).indicator (fun g => PsiK ε f w (S7.toM g)) g ∂Measure.haar < ⊤ := by
  classical
  set V : Set (S7.UJ ε) := U ∩ {g | R₂ < Formalism.REAL.hs (S7.toM g)} with hV
  have hVm : MeasurableSet V :=
    hUm.inter (measurableSet_lt measurable_const ((continuous_hs.comp (S7.continuous_toM ε)).measurable))
  have hinj : Function.Injective (fun g : S7.UJ ε => S7.toM g) := (S7.isClosedEmbedding_toM ε).injective
  set F : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞ := ((fun g : S7.UJ ε => S7.toM g) '' V).indicator (PsiK ε f w) with hFdef
  have hF : ∀ g : S7.UJ ε, F (S7.toM g) = V.indicator (fun g => PsiK ε f w (S7.toM g)) g := by
    intro g
    by_cases hg : g ∈ V
    · rw [Set.indicator_of_mem hg, hFdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hg)]
    · rw [Set.indicator_apply, if_neg hg, hFdef, Set.indicator_apply, if_neg]
      rintro ⟨g', hg', he⟩
      exact hg (hinj he ▸ hg')
  have hFm : Measurable fun g : S7.UJ ε => F (S7.toM g) := by
    rw [show (fun g : S7.UJ ε => F (S7.toM g)) = V.indicator (fun g => PsiK ε f w (S7.toM g)) from funext hF]
    exact (psiK_meas f w (H.cont f hf)).indicator hVm
  have hFK : ∀ (g : S7.UJ ε) (k : S7.KG ε), F (S7.toM g * S7.toMK k) = F (S7.toM g) := by
    intro g k
    have e : S7.toM g * S7.toMK k = S7.toM (g * (k : S7.UJ ε)) := rfl
    have hsk : Formalism.REAL.hs (S7.toM (g * (k : S7.UJ ε))) = Formalism.REAL.hs (S7.toM g) := hs_mul_K _ k
    have hmem : g * (k : S7.UJ ε) ∈ V ↔ g ∈ V := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · have := hUK _ k⁻¹ h1
          simpa [mul_assoc] using this
        · show R₂ < Formalism.REAL.hs (S7.toM g)
          have h2' : R₂ < Formalism.REAL.hs (S7.toM (g * (k : S7.UJ ε))) := h2
          rw [hsk] at h2'
          exact h2'
      · rintro ⟨h1, h2⟩
        refine ⟨hUK g k h1, ?_⟩
        show R₂ < Formalism.REAL.hs (S7.toM (g * (k : S7.UJ ε)))
        rw [hsk]
        exact h2
    rw [e, hF, hF]
    by_cases hg : g ∈ V
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.2 hg)]
      exact psiK_inv f w g k
    · rw [Set.indicator_apply, if_neg (fun h => hg (hmem.1 h)), Set.indicator_apply, if_neg hg]
  obtain ⟨T, Cf, hTS, hd⟩ := H.dom f hf
  have hle := fun h (hh : h ∈ T) => line_est hLC H hn s hs hL c'' hc0 hc1 j hz h (hTS h hh)
  choose! Ψ K hKT hΨm hΨK hΨi hΨae using hle
  set Kr : ℝ := C ^ (-s) * Real.exp (2 * c'') with hKr
  set Ψt : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞ := fun X => ∑ h ∈ T, Ψ h X with hΨt
  have hΨtm : Measurable fun g : S7.UJ ε => Ψt (S7.toM g) := Finset.measurable_sum _ fun h hh => hΨm h hh
  have hΨtK : ∀ (g : S7.UJ ε) (k : S7.KG ε), Ψt (S7.toM g * S7.toMK k) = Ψt (S7.toM g) :=
    fun g k => Finset.sum_congr rfl fun h hh => hΨK h hh g k
  have hΨti : ∫⁻ g : S7.UJ ε, Ψt (S7.toM g) ∂Measure.haar < ⊤ := by
    rw [lintegral_finsetSum _ (fun h hh => hΨm h hh)]
    exact ENNReal.sum_lt_top.2 fun h hh => hΨi h hh
  obtain ⟨κ, hκ0, hκT, hform⟩ := H.formula j
  set slab : Set (PSub ε (A j)) := {x : PSub ε (A j) | τ j x ∈ Set.Ico 0 1} with hslabdef
  have hslab : MeasurableSet slab :=
    ((H.tauCont j).measurable.comp measurable_subtype_coe) measurableSet_Ico
  have hJ : ∫⁻ x in slab,
      (∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j) < ⊤ := by
    have e := hform Ψt hΨtm hΨtK
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top hκ0] at e
    rw [e] at hΨti
    exact lt_irrefl _ hΨti
  have inner : ∀ x : PSub ε (A j), τ j x ∈ Set.Ico 0 1 →
      ∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) ≤
        ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T,
          ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) *
            ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)) := by
    intro x hx
    have hb : 1 ≤ Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) := one_le_hs hn _
    have pt : ∀ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) ≤
        (Set.Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T,
          ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) * (‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)))) t := by
      intro t
      obtain ⟨y, hy, hτy⟩ := H.lines j x t
      have hFy : F (S7.toM (x : S7.UJ ε) * aT (A j) t) = V.indicator (fun g => PsiK ε f w (S7.toM g)) (y : S7.UJ ε) := by
        rw [← hy]; exact hF _
      rw [hFy]
      by_cases hyV : (y : S7.UJ ε) ∈ V
      · obtain ⟨hyU, hyR⟩ := hyV
        have hyR' : R₂ < Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) := hyR
        have hlog := hUτ y hyU
        have hτ1 : 1 < τ j y := by
          have hl : Real.log R₂ < Real.log (Formalism.REAL.hs (S7.toM (y : S7.UJ ε))) :=
            Real.log_lt_log (by linarith) hyR'
          have := mul_lt_mul_of_pos_left hl H.c1pos
          linarith
        have ht : 0 < t := by have := hx.2; linarith
        rw [Set.indicator_of_mem (show (y : S7.UJ ε) ∈ V from ⟨hyU, hyR⟩), Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
        have hline := H.hsLine j x t hx.1 ht.le
        rw [← hy] at hline
        have hreal := far_real (Formalism.REAL.hs (S7.toM (y : S7.UJ ε))) (Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) C c₁ s w c''
          (r j) t (τ j y) (τ j x) (by linarith) hb hline.1 hline.2 hlog hτy hx.2 H.c1pos hs hw1 hw2 hc0
        calc PsiK ε f w (S7.toM (y : S7.UJ ε)) * ENNReal.ofReal (Real.exp (2 * r j * t))
            ≤ (ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
                ENNReal.ofReal (Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ w)) * ENNReal.ofReal (Real.exp (2 * r j * t)) :=
              mul_le_mul_left (psiK_le f w T Cf hd y) _
          _ = ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
                ENNReal.ofReal (Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ w * Real.exp (2 * r j * t)) := by
              rw [mul_assoc, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl fun h _ => ?_
              rw [ENNReal.ofReal_mul' (Real.exp_pos _).le, mul_assoc]
          _ ≤ ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
                ENNReal.ofReal (Kr * Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s * Real.exp (2 * (r j + s + c'') * t)) :=
              mul_le_mul_right (Finset.sum_le_sum fun h _ => mul_le_mul_right (ENNReal.ofReal_le_ofReal hreal) _) _
          _ = _ := by
              rw [hy]
              simp only [Finset.mul_sum]
              refine Finset.sum_congr rfl fun h _ => ?_
              rw [ENNReal.ofReal_mul' (Real.exp_pos _).le, ENNReal.ofReal_mul' (by positivity)]
              ring
      · rw [Set.indicator_apply, if_neg hyV, zero_mul]
        exact bot_le
    have hmeas : ∀ h ∈ T, Measurable fun t : ℝ => ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) *
        (‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t))) := by
      intro h hh
      have hc := line_cont H j x h (H.cont h (hTS h hh))
      exact measurable_const.mul ((hc.enorm.measurable.pow_const 2).mul
        (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable))
    calc ∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))
        ≤ ∫⁻ t : ℝ, (Set.Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T,
          ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) * (‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)))) t := lintegral_mono pt
      _ = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T,
          ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) * (‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t))) := lintegral_indicator measurableSet_Ioi _
      _ = _ := by
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
            lintegral_finsetSum _ hmeas]
          congr 1
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  set Kall : ℝ≥0∞ := ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T, K h with hKall_def
  have hKall : Kall ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.sum_ne_top.2 fun h hh => hKT h hh)
  have hae : ∀ᵐ (x : PSub ε (A j)) ∂((ν j).restrict slab),
      ∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) ≤
        Kall * ∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
    rw [ae_restrict_iff' hslab]
    have hall := (Filter.eventually_all_finset T).2 fun h hh => hΨae h hh
    filter_upwards [hall] with x hx hxs
    calc _ ≤ _ := inner x hxs
      _ ≤ ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T, K h *
            ∫⁻ t : ℝ, Ψ h (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) :=
          mul_le_mul_right (Finset.sum_le_sum fun h hh => hx h hh hxs) _
      _ ≤ ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T, K h *
            ∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
          refine mul_le_mul_right (Finset.sum_le_sum fun h hh => mul_le_mul_right (lintegral_mono fun t => ?_) _) _
          exact mul_le_mul_left (Finset.single_le_sum (f := fun h => Ψ h (S7.toM (x : S7.UJ ε) * aT (A j) t))
            (fun _ _ => bot_le) hh) _
      _ = Kall * ∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
          rw [hKall_def, ← Finset.sum_mul]; ring
  have hI : ∫⁻ x in slab,
      (∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j) < ⊤ := by
    calc _ ≤ ∫⁻ x in slab,
          Kall * (∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j) :=
          lintegral_mono_ae hae
      _ = Kall * ∫⁻ x in slab,
          (∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j) :=
          lintegral_const_mul' _ _ hKall
      _ < ⊤ := ENNReal.mul_lt_top hKall.lt_top hJ
  have e1 : (∫⁻ g : S7.UJ ε, V.indicator (fun g => PsiK ε f w (S7.toM g)) g ∂Measure.haar) =
      ∫⁻ g : S7.UJ ε, F (S7.toM g) ∂Measure.haar := by
    congr 1; funext g; exact (hF g).symm
  rw [e1, hform F hFm hFK]
  exact ENNReal.mul_lt_top hκT.lt_top hI

theorem ball_est (hn : 0 < n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (s w R₂ : ℝ) (hw : s ≤ w) (hR₂ : 1 ≤ R₂)
    (hf : LevelF ε f s) :
    ∫⁻ g : S7.UJ ε, {g | Formalism.REAL.hs (S7.toM g) ≤ R₂}.indicator
      (fun g => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w)) g ∂Measure.haar < ⊤ := by
  unfold LevelF at hf
  have key : ∀ g : S7.UJ ε, {g | Formalism.REAL.hs (S7.toM g) ≤ R₂}.indicator
      (fun g => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w)) g ≤
      ENNReal.ofReal (R₂ ^ (w - s)) * (‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s)) := by
    intro g
    by_cases hg : Formalism.REAL.hs (S7.toM g) ≤ R₂
    · rw [Set.indicator_of_mem (show g ∈ {g | Formalism.REAL.hs (S7.toM g) ≤ R₂} from hg)]
      have h1 := one_le_hs hn g
      have hpos : 0 < Formalism.REAL.hs (S7.toM g) := by linarith
      have e : Formalism.REAL.hs (S7.toM g) ^ w = Formalism.REAL.hs (S7.toM g) ^ s * Formalism.REAL.hs (S7.toM g) ^ (w - s) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      have hle : Formalism.REAL.hs (S7.toM g) ^ (w - s) ≤ R₂ ^ (w - s) :=
        Real.rpow_le_rpow hpos.le hg (by linarith)
      rw [e, ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)]
      calc ‖f (S7.toM g)‖ₑ ^ 2 * (ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (w - s)))
          ≤ ‖f (S7.toM g)‖ₑ ^ 2 * (ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) * ENNReal.ofReal (R₂ ^ (w - s))) := by
            gcongr
        _ = _ := by ring
    · rw [Set.indicator_of_notMem (show g ∉ {g | Formalism.REAL.hs (S7.toM g) ≤ R₂} from hg)]
      exact bot_le
  refine lt_of_le_of_lt (lintegral_mono key) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

theorem step (hLC : LineChain) (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (hn : 0 < n) (s : ℝ) (hs : s ≤ 0) (hL : ∀ f ∈ S, LevelF ε f s)
    (c'' : ℝ) (hc0 : 0 < c'') (hc1 : c'' ≤ 1) (hz : ∀ j, ∀ z ∈ Z j, z.re ≠ -(r j + s + c''))
    (w : ℝ) (hw1 : s ≤ w) (hw2 : w ≤ s + 2 * c₁ * c'') : ∀ f ∈ S, LevelF ε f w := by
  obtain ⟨U, hUm, hUK, hUcov, hUτ⟩ := H.cover
  set R₂ : ℝ := max (max R₀ 1) (Real.exp (1 / c₁)) with hR₂def
  have hR₂1 : 1 ≤ R₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR₂0 : R₀ ≤ R₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR₂' : 1 ≤ c₁ * Real.log R₂ := by
    have h1 : 1 / c₁ ≤ Real.log R₂ := by
      rw [← Real.log_exp (1 / c₁)]
      exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    have hc := H.c1pos
    calc (1:ℝ) = c₁ * (1 / c₁) := by field_simp
      _ ≤ c₁ * Real.log R₂ := by gcongr
  intro f hf
  have hcont := H.cont f hf
  have hmhs : Measurable fun g : S7.UJ ε => Formalism.REAL.hs (S7.toM g) :=
    (continuous_hs.comp (S7.continuous_toM ε)).measurable
  set ball : S7.UJ ε → ℝ≥0∞ := {g | Formalism.REAL.hs (S7.toM g) ≤ R₂}.indicator
      (fun g => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w)) with hball
  set far : Fin m → S7.UJ ε → ℝ≥0∞ := fun j => (U j ∩ {g | R₂ < Formalism.REAL.hs (S7.toM g)}).indicator
      (fun g => PsiK ε f w (S7.toM g)) with hfar
  have hmball : Measurable ball := by
    refine Measurable.indicator ?_ (measurableSet_le hmhs measurable_const)
    exact (hcont.enorm.measurable.pow_const 2).mul ((hmhs.pow_const w).ennreal_ofReal)
  have hmfar : ∀ j ∈ (Finset.univ : Finset (Fin m)), Measurable (far j) := fun j _ =>
    (psiK_meas f w hcont).indicator ((hUm j).inter (measurableSet_lt measurable_const hmhs))
  have hpt : ∀ g, ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) ≤ ball g + ∑ j, far j g := by
    intro g
    by_cases hg : Formalism.REAL.hs (S7.toM g) ≤ R₂
    · have e : ball g = ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) :=
        Set.indicator_of_mem (show g ∈ {g | Formalism.REAL.hs (S7.toM g) ≤ R₂} from hg) _
      rw [e]; exact le_self_add
    · push_neg at hg
      obtain ⟨j, hj⟩ := hUcov g (lt_of_le_of_lt hR₂0 hg)
      have hfj : far j g = PsiK ε f w (S7.toM g) :=
        Set.indicator_of_mem (show g ∈ U j ∩ {g | R₂ < Formalism.REAL.hs (S7.toM g)} from ⟨hj, hg⟩) _
      calc _ ≤ PsiK ε f w (S7.toM g) := psiK_ge f w g
        _ = far j g := hfj.symm
        _ ≤ ∑ j, far j g := Finset.single_le_sum (f := fun j => far j g) (fun _ _ => bot_le) (Finset.mem_univ j)
        _ ≤ _ := le_add_self
  unfold LevelF
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_add_left hmball, lintegral_finset_sum _ hmfar]
  refine ENNReal.add_lt_top.2 ⟨ball_est hn f s w R₂ hw1 hR₂1 (hL f hf), ?_⟩
  exact ENNReal.sum_lt_top.2 fun j _ => far_est hLC H hn s hs hL c'' hc0 hc1 j (hz j) (U j) (hUm j)
    (fun g k hg => hUK j g k hg) (hUτ j) R₂ hR₂1 hR₂' w hw1 hw2 f hf

theorem exists_good (Z : Fin m → Finset ℂ) (r : Fin m → ℝ) (s : ℝ) :
    ∃ c'' : ℝ, 1 / 2 ≤ c'' ∧ c'' ≤ 1 ∧ ∀ j, ∀ z ∈ Z j, z.re ≠ -(r j + s + c'') := by
  classical
  set B : Finset ℝ := Finset.univ.biUnion (fun j => (Z j).image (fun z => -(r j + s) - z.re))
  obtain ⟨c, hc, hcB⟩ := (Set.Icc_infinite (show (1 / 2 : ℝ) < 1 by norm_num)).exists_notMem_finset B
  refine ⟨c, hc.1, hc.2, fun j z hz he => hcB ?_⟩
  simp only [B, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  exact ⟨j, z, hz, by linarith⟩

theorem level_mono (hn : 0 < n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) {s s' : ℝ} (h : s' ≤ s) (hf : LevelF ε f s) :
    LevelF ε f s' := by
  unfold LevelF at *
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hf
  gcongr
  exact one_le_hs hn g

theorem level_zero_dim (ε : Fin 0 → Bool) (f : Matrix (Fin 0) (Fin 0) ℂ → ℂ) (s : ℝ) : LevelF ε f s := by
  unfold LevelF
  haveI : Subsingleton (S7.UJ ε) := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  haveI : CompactSpace (S7.UJ ε) := Finite.compactSpace
  set c : ℝ≥0∞ := ‖f (S7.toM (1 : S7.UJ ε))‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM (1 : S7.UJ ε)) ^ s)
  have : ∀ g : S7.UJ ε, ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) = c := by
    intro g; rw [Subsingleton.elim g 1]
  simp_rw [this]
  rw [lintegral_const]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top) (measure_lt_top _ _)

theorem absolute_l2_of_line_chain (hLC : LineChain) : AbsoluteL2Bound := by
  intro n ε S m A ν τ r Z M c₁ R₀ C hc1 hform htc htinv hlines hcover hhs hcont hdom hchain hqual hlev
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact fun f _ => level_zero_dim ε f 0
  have H : Hyp ε S m A ν τ r Z M c₁ R₀ C :=
    ⟨hc1, hform, htc, htinv, hlines, hcover, hhs, hcont, hdom, hchain, hqual, hlev⟩
  have key : ∀ N : ℕ, ∀ f ∈ S, LevelF ε f (min (-M + N * c₁) 0) := by
    intro N
    induction N with
    | zero =>
      intro f hf
      exact level_mono hn f (by simp) (hlev f hf)
    | succ N ih =>
      obtain ⟨c'', h1, h2, hz⟩ := exists_good Z r (min (-M + N * c₁) 0)
      refine step hLC H hn _ (min_le_right _ _) ih c'' (by linarith) h2 hz _ ?_ ?_
      · apply min_le_min_right; push_cast; nlinarith [hc1]
      · have hcc : c₁ ≤ 2 * c₁ * c'' := by nlinarith
        rcases le_total (-M + N * c₁) 0 with h | h
        · rw [min_eq_left h]; push_cast
          have := min_le_left (-M + ((N : ℝ) + 1) * c₁) 0; nlinarith
        · rw [min_eq_right h]
          have := min_le_right (-M + ((N + 1 : ℕ) : ℝ) * c₁) 0; nlinarith
  intro f hf
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M ≤ N * c₁ := ⟨⌈M / c₁⌉₊, by
    have := Nat.le_ceil (M / c₁); rwa [div_le_iff₀ hc1] at this⟩
  have := key N f hf
  rwa [min_eq_right (by linarith)] at this

end CompanionTheory.RgExh.Dec.L.AB
