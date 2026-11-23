import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeSubHaar

open Topology

open MeasureTheory NumberField Matrix Finset in
open Topology in
private theorem uMat_one_flag_measures {n : ℕ} {ε : Fin n → Bool} : _root_.Formalism.MainNotions.S.uMat (1 : _root_.Formalism.REAL.UJ ε) = 1 := by
  have h1 := _root_.GlobalTheory.GaugeSubLoc.uMat_mul (1 : _root_.Formalism.REAL.UJ ε) 1
  have h2 := _root_.GlobalTheory.GaugeSubLoc.uMat_mul_inv (1 : _root_.Formalism.REAL.UJ ε)
  rw [mul_one] at h1
  rw [inv_one, ← h1] at h2
  exact h2

open MeasureTheory NumberField Matrix Finset in
open Topology in
private theorem comap_subtype_val_haar_properties {n : ℕ} {ε : Fin n → Bool}
    (S : Subgroup (_root_.Formalism.REAL.UJ ε)) (hS : IsClosed (S : Set (_root_.Formalism.REAL.UJ ε))) (d : ℕ)
    (μ : Measure (_root_.Formalism.REAL.UJ ε)) (h : _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ) :
    Measure.map (Subtype.val : S → _root_.Formalism.REAL.UJ ε) (μ.comap Subtype.val) = μ ∧
      (μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)) ∧
      μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) ≠ 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hme : MeasurableEmbedding (Subtype.val : S → _root_.Formalism.REAL.UJ ε) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  set ν := μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν
  have hmap : Measure.map Subtype.val ν = μ := by
    rw [hme.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 h1)
  have hinv : ν.IsMulLeftInvariant := by
    refine ⟨fun s => ?_⟩
    have key : Measure.map Subtype.val (Measure.map (s * ·) ν) = Measure.map Subtype.val ν := by
      rw [Measure.map_map hme.measurable (measurable_const_mul s)]
      have hcomp : (Subtype.val ∘ (s * ·)) =
          (fun g : _root_.Formalism.REAL.UJ ε => (s : _root_.Formalism.REAL.UJ ε) * g) ∘ Subtype.val := by
        funext x; rfl
      rw [hcomp, ← Measure.map_map (measurable_const_mul _) hme.measurable, hmap]
      exact h2 s s.2
    have := congrArg (Measure.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)) key
    rwa [hme.comap_map, hme.comap_map] at this
  set f : _root_.Formalism.REAL.UJ ε → ℝ := fun g => √(_root_.Formalism.REAL.hs (_root_.Formalism.MainNotions.S.uMat g - 1)) with hfdef
  have hf : Continuous f := by
    simp only [hfdef, _root_.Formalism.REAL.hs]
    have := _root_.GlobalTheory.GaugeConst.continuous_uMat ε
    fun_prop
  have hf1 : f 1 = 0 := by simp [hfdef, _root_.Formalism.REAL.hs, uMat_one_flag_measures]
  revert h3
  change Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) → _
  intro h3
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hev := (h3.eventually (isOpen_Ioo.mem_nhds ⟨pos_iff_ne_zero.2 hL0, lt_top_iff_ne_top.2 hLtop⟩)).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)
  obtain ⟨r, ⟨hpos, htop⟩, hr⟩ := hev.exists
  set B := {g | f g ≤ r} with hBdef
  have hB0 : μ B ≠ 0 := by
    intro h0
    change 0 < μ B / _ at hpos
    rw [h0, ENNReal.zero_div] at hpos
    exact lt_irrefl _ hpos
  have hBtop : μ B ≠ ⊤ := by
    intro h0
    change μ B / _ < ⊤ at htop
    rw [h0, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at htop
    exact lt_irrefl _ htop
  have hνB : ν (Subtype.val ⁻¹' B) = μ B := by rw [← hme.map_apply, hmap]
  refine ⟨hmap, hinv, ?_, ?_⟩
  · refine ⟨fun K hK => ?_⟩
    have hUo : IsOpen (Subtype.val ⁻¹' {g | f g < r} : Set S) :=
      (isOpen_lt hf continuous_const).preimage continuous_subtype_val
    have hUne : (Subtype.val ⁻¹' {g | f g < r} : Set S).Nonempty :=
      ⟨1, by simp only [Set.mem_preimage, Set.mem_setOf_eq, OneMemClass.coe_one, hf1]; exact hr⟩
    have hUtop : ν (Subtype.val ⁻¹' {g | f g < r}) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (Set.preimage_mono
        (show {g | f g < r} ⊆ B from fun g (hg : f g < r) => (le_of_lt hg : f g ≤ r))))
      rw [hνB]; exact hBtop
    exact measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hUo hUne hUtop hK
  · intro h0
    apply hB0
    rw [← hνB, h0, Measure.coe_zero, Pi.zero_apply]

open MeasureTheory NumberField Matrix Finset in
open Topology in

theorem _root_.GlobalTheory.GaugeSubHaar.isGaugeSub_haar : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (_root_.Formalism.REAL.UJ ε)), IsClosed (S : Set (_root_.Formalism.REAL.UJ ε)) → ∀ (d : ℕ) (μ : Measure (_root_.Formalism.REAL.UJ ε)), _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ ∀ μ', _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ' → μ' = μ := by
  intro n ε S hS d μ hμ
  have hme : MeasurableEmbedding (Subtype.val : S → _root_.Formalism.REAL.UJ ε) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  obtain ⟨hmap, hinv, hfin, hne⟩ := comap_subtype_val_haar_properties S hS d μ hμ
  set ν := μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν
  have hfinμ : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [← hmap, hme.map_apply]
    exact (hS.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top⟩
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.Formalism.REAL.UJ ε) := inferInstance
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨inferInstance, hfinμ, fun μ' hμ' => ?_⟩
  obtain ⟨hmap', hinv', hfin', -⟩ := comap_subtype_val_haar_properties S hS d μ' hμ'
  set ν' := μ'.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν'
  have hcover : ∃ k, ν (compactCovering S k) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
    exact measure_iUnion_null hcon
  obtain ⟨k, hk⟩ := hcover
  haveI : ν.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering S k) hk
  haveI : ν.IsHaarMeasure := { }
  have hsmul := Measure.isMulLeftInvariant_eq_smul ν' ν
  set c := ν'.haarScalarFactor ν with hc
  have hμc : μ' = c • μ := by
    rw [← hmap', hsmul, Measure.map_smul, hmap]
  obtain ⟨-, -, h3⟩ := hμ
  obtain ⟨-, -, h3'⟩ := hμ'
  rw [hμc] at h3'
  revert h3 h3'
  change Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) →
    Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) → _
  intro h3 h3'
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h4 := ENNReal.Tendsto.const_mul h3 (Or.inr (ENNReal.coe_ne_top (r := c)))
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc] at h3'
  have heq := tendsto_nhds_unique h4 h3'
  have hc1 : (c : ENNReal) = 1 := by
    rw [← ENNReal.mul_left_inj hL0 hLtop, one_mul]
    exact heq
  rw [hμc, ENNReal.coe_eq_one.1 hc1, one_smul]

end GlobalTheory.GaugeSubHaar
