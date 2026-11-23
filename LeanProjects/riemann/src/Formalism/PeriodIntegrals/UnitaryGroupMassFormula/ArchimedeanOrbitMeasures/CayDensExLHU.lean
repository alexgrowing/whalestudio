import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExCayH

noncomputable section

namespace HcInf

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Pointwise

section LHU

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem lhu_right (m : Measure G) [m.IsHaarMeasure] (z : G) :
    ∃ r : ℝ≥0∞, ∀ B : Set G, MeasurableSet B → m {x | x * z ∈ B} = r * m B := by
  have hmeas : Measurable (fun x : G => x * z) := measurable_mul_const z
  haveI : (m.map (fun x : G => x * z)).IsMulLeftInvariant := ⟨fun g => by
    rw [Measure.map_map (measurable_const_mul g) hmeas]
    have hc : ((fun x : G => g * x) ∘ fun x => x * z) = (fun x => x * z) ∘ fun x => g * x := by
      funext x; simp [mul_assoc]
    rw [hc, ← Measure.map_map hmeas (measurable_const_mul g), map_mul_left_eq_self]⟩
  haveI : IsFiniteMeasureOnCompacts (m.map (fun x : G => x * z)) := ⟨fun K hK => by
    rw [Measure.map_apply hmeas hK.measurableSet]
    exact ((Homeomorph.mulRight z).isCompact_preimage.2 hK).measure_lt_top⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, m.map (fun x : G => x * z) = c • m :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun B hB => ?_⟩
  show m ((fun x : G => x * z) ⁻¹' B) = _
  rw [← Measure.map_apply hmeas hB, hc, Measure.coe_nnreal_smul_apply]

theorem lhu_key (m : Measure G) [m.IsHaarMeasure] (β : Measure G) (W V : Set G)
    (hinv : ∀ (h : G) (S : Set G), MeasurableSet S → S ⊆ W → (fun g => h * g) '' S ⊆ W →
      β ((fun g => h * g) '' S) = β S)
    (hVc : IsCompact V) (hVW : V ⊆ W) (hVW' : ∀ v ∈ V, v⁻¹ ∈ W) (hβV : β V ≠ ⊤) (hβVi : β V⁻¹ ≠ ⊤) :
    ∃ K : ℝ≥0∞, ∀ B : Set G, MeasurableSet B → B ⊆ V → m V * β B = K * m B := by

  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  have hVim : MeasurableSet V⁻¹ := hVc.inv.isClosed.measurableSet
  have hViW : V⁻¹ ⊆ W := fun x hx => by simpa using hVW' x⁻¹ hx
  choose r hr using fun z => lhu_right m z
  refine ⟨∫⁻ x in V⁻¹, r x ∂β, fun B hB hBV => ?_⟩
  haveI : IsFiniteMeasure (β.restrict V⁻¹) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hβVi⟩
  haveI : IsFiniteMeasure (β.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono hBV) (lt_top_iff_ne_top.2 hβV)⟩
  have hmB : m B ≠ ⊤ := ne_top_of_le_ne_top hVc.measure_lt_top.ne (measure_mono hBV)
  have hE : MeasurableSet {p : G × G | p.2 * p.1 ∈ B} := (measurable_snd.mul measurable_fst) hB
  have hF : MeasurableSet {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} :=
    (measurable_snd.inv.mul measurable_fst) hVim
  have ha : ((β.restrict V⁻¹).prod m) {p : G × G | p.2 * p.1 ∈ B}
      = (∫⁻ x in V⁻¹, r x ∂β) * m B := by
    rw [Measure.prod_apply hE]
    calc _ = ∫⁻ x, r x * m B ∂(β.restrict V⁻¹) := lintegral_congr (fun x => hr x B hB)
      _ = (∫⁻ x in V⁻¹, r x ∂β) * m B := lintegral_mul_const' _ _ hmB
  have h1 : ∀ t : G, (β.restrict V⁻¹) ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B})
      = (β.restrict B) ((fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) := by
    intro t
    have hS : MeasurableSet ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B}) :=
      measurable_const_mul t hB
    have hT : MeasurableSet ((fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) :=
      measurable_const_mul t⁻¹ hVim
    rw [Measure.restrict_apply hS, Measure.restrict_apply hT]
    have himg : (fun g => t * g) '' ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B} ∩ V⁻¹)
        = (fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} ∩ B := by
      ext y
      constructor
      · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
        refine ⟨?_, hx1⟩
        show t⁻¹ * (t * x) ∈ V⁻¹
        rwa [inv_mul_cancel_left]
      · rintro ⟨hy1, hy2⟩
        refine ⟨t⁻¹ * y, ⟨?_, hy1⟩, mul_inv_cancel_left t y⟩
        show t * (t⁻¹ * y) ∈ B
        rwa [mul_inv_cancel_left]
    have hsub : (fun g => t * g) '' ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B} ∩ V⁻¹) ⊆ W := by
      rw [himg]; exact fun y hy => hVW (hBV hy.2)
    rw [← himg]
    exact (hinv t _ (hS.inter hVim) (fun x hx => hViW hx.2) hsub).symm
  have hb : ((β.restrict V⁻¹).prod m) {p : G × G | p.2 * p.1 ∈ B} = m V * β B := by
    rw [Measure.prod_apply_symm hE]
    calc _ = ∫⁻ t, (β.restrict B) ((fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) ∂m :=
          lintegral_congr h1
      _ = ((β.restrict B).prod m) {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} :=
          (Measure.prod_apply_symm hF).symm
      _ = ∫⁻ y, m (Prod.mk y ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) ∂(β.restrict B) :=
          Measure.prod_apply hF
      _ = ∫⁻ y, m V ∂(β.restrict B) := by
          refine lintegral_congr (fun y => ?_)
          have hpre : Prod.mk y ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} = (fun t => y⁻¹ * t) ⁻¹' V := by
            ext t; simp [mul_inv_rev]
          rw [hpre, measure_preimage_mul]
      _ = m V * β B := by rw [lintegral_const, Measure.restrict_apply_univ]
  exact hb.symm.trans ha

theorem local_haar_unique : LocalHaarUnique := by
  intro G _ _ _ _ _ _ _ _ m hm β W hWo h1W hinv hfin hβW
  have hU : W ∩ W⁻¹ ∈ 𝓝 (1 : G) :=
    Filter.inter_mem (hWo.mem_nhds h1W) (hWo.inv.mem_nhds (by simpa using h1W))
  obtain ⟨V, hV1, hVsub, hVc⟩ := local_compact_nhds hU
  have hVW : V ⊆ W := fun x hx => (hVsub hx).1
  have hVW' : ∀ v ∈ V, v⁻¹ ∈ W := fun v hv => (hVsub hv).2
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  have hβV : β V ≠ ⊤ := hfin V hVc hVW
  have hβVi : β V⁻¹ ≠ ⊤ := hfin V⁻¹ hVc.inv (fun x hx => by simpa using hVW' x⁻¹ hx)
  have h1V : (1 : G) ∈ interior V := mem_interior_iff_mem_nhds.2 hV1
  have hmV0 : m V ≠ 0 :=
    ((isOpen_interior.measure_pos m ⟨1, h1V⟩).trans_le (measure_mono interior_subset)).ne'
  have hmVt : m V ≠ ⊤ := hVc.measure_lt_top.ne

  have hβV0 : β V ≠ 0 := by
    intro h0
    apply hβW
    let U : G → Set G := fun w => W ∩ (fun x => w⁻¹ * x) ⁻¹' interior V
    have hUo : ∀ w, IsOpen (U w) := fun w =>
      hWo.inter (isOpen_interior.preimage (continuous_const.mul continuous_id))
    have hU0 : ∀ w, β (U w) = 0 := by
      intro w
      have hSm : MeasurableSet ((fun x => w * x) ⁻¹' U w) :=
        measurable_const_mul w (hUo w).measurableSet
      have hSV : (fun x => w * x) ⁻¹' U w ⊆ V := by
        intro x hx
        have hx2 := hx.2
        simp only [Set.mem_preimage, inv_mul_cancel_left] at hx2
        exact interior_subset hx2
      have himg : (fun g => w * g) '' ((fun x => w * x) ⁻¹' U w) = U w :=
        Set.image_preimage_eq _ (mul_left_surjective w)
      have h := hinv w _ hSm (hSV.trans hVW) (by rw [himg]; exact fun y hy => hy.1)
      rw [himg] at h
      rw [h]
      exact measure_mono_null hSV h0
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
    have hWU : W ⊆ ⋃ w ∈ T, U w := by
      rw [hTU]
      intro x hx
      exact Set.mem_iUnion.2 ⟨x, hx, by simpa using h1V⟩
    exact measure_mono_null hWU ((measure_biUnion_null_iff hTc).2 (fun w _ => hU0 w))
  obtain ⟨K, hK⟩ := lhu_key m β W V hinv hVc hVW hVW' hβV hβVi
  refine ⟨β V / m V, (ENNReal.div_pos hβV0 hmVt).ne', ENNReal.div_ne_top hβV hmV0, V, hV1, hVW, ?_⟩
  ext s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  have h1 := hK (s ∩ V) (hs.inter hVm) (fun x hx => hx.2)
  have h2 := hK V hVm subset_rfl
  have e1 : β (s ∩ V) = (m V)⁻¹ * (K * m (s ∩ V)) := by
    rw [← h1, ← mul_assoc, ENNReal.inv_mul_cancel hmV0 hmVt, one_mul]
  have e2 : β V = (m V)⁻¹ * (K * m V) := by
    rw [← h2, ← mul_assoc, ENNReal.inv_mul_cancel hmV0 hmVt, one_mul]
  rw [e1, div_eq_mul_inv, e2]
  calc (m V)⁻¹ * (K * m (s ∩ V)) = (m V)⁻¹ * K * (m V * (m V)⁻¹) * m (s ∩ V) := by
        rw [ENNReal.mul_inv_cancel hmV0 hmVt, mul_one, mul_assoc]
    _ = (m V)⁻¹ * (K * m V) * (m V)⁻¹ * m (s ∩ V) := by ring

end LHU

end HcInf
