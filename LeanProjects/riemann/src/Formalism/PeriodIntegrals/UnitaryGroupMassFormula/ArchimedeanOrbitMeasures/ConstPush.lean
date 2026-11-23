import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstSm

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def FrameIndependentAtInfinity : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → Y0 X u' ∈ IndI X

def ProperOrb : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ K : Set (TupI X), IsCompact K → K ⊆ IndI X →
      ∃ N ∈ 𝓝 (1 : MfI X), ∃ C : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J), IsCompact C ∧
        ∀ b ∈ N, ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • rmulT X b (Y0 X u') ∈ K → g ∈ C

theorem continuous_smul_left {D : D7} (X : HidaSetting D) (y : TupI X) :
    Continuous (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (y a)
  exact (MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).matrix_mulVec continuous_const

theorem continuous_rmulT {D : D7} (X : HidaSetting D) (Y : TupI X) : Continuous (fun b : MfI X => rmulT X b Y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun b => continuous_pi fun i => ?_
  simp only [rmulT]
  exact continuous_finsetSum _ fun c _ => (continuous_apply_apply c b).mul continuous_const

theorem pushCont_of (hY : FrameIndependentAtInfinity) (hPr : ProperOrb) : PushCont := by
  intro D X u' ψ hT μinf νinf fibInf hH a ha1 hac
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have : SecondCountableTopology (MfI X) :=
    inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : SecondCountableTopology (HmI X) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hY0 := hY X u' ψ hT μinf νinf fibInf hH
  obtain ⟨V, hVo, hYV, hVc, -⟩ := exists_open_between_and_isCompact_closure isCompact_singleton (isOpen_IndI X)
    (Set.singleton_subset_iff.2 hY0)
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact isCompact_singleton hVo.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 hYV)
  have hsupp : Function.support f ⊆ V := fun y hy => by
    by_contra h; exact hy (hf0 h)
  have htsupp : tsupport f ⊆ IndI X := (closure_mono hsupp).trans hVc
  have hfY : f (Y0 X u') = 1 := hf1 (Set.mem_singleton _)
  obtain ⟨N, hN, C, hC, hNC⟩ := hPr X u' ψ hT μinf νinf fibInf hH (tsupport f) hfc.isCompact htsupp
  have hbound : ∀ b ∈ N, ∀ g, ENNReal.ofReal (f (g • rmulT X b (Y0 X u'))) ≤ C.indicator 1 g := by
    intro b hb g
    by_cases hg : f (g • rmulT X b (Y0 X u')) = 0
    · rw [hg, ENNReal.ofReal_zero]; exact bot_le
    · have hgC : g ∈ C := hNC b hb g (subset_tsupport _ hg)
      rw [Set.indicator_of_mem hgC, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hfI _).2
  have h1N : (1 : MfI X) ∈ N := mem_of_mem_nhds hN
  have hCfin : ∫⁻ g, C.indicator 1 g ∂X.measG.μGinf < ⊤ :=
    lt_of_le_of_lt (lintegral_indicator_one_le C) hC.measure_lt_top
  refine ⟨f, f.continuous, f.continuous.measurable, hfc, htsupp, fun y => (hfI y).1, ?_, ?_, ?_⟩
  · have hm : Measurable fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => ENNReal.ofReal (f (g • Y0 X u')) :=
      ENNReal.measurable_ofReal.comp (f.continuous.comp (continuous_smul_left X (Y0 X u'))).measurable
    rw [lintegral_pos_iff_support hm]
    have hOo : IsOpen ((fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {y | 0 < f y}) :=
      (isOpen_lt continuous_const f.continuous).preimage (continuous_smul_left X (Y0 X u'))
    have h1O : (1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
        (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {y | 0 < f y} := by
      show 0 < f ((1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) • Y0 X u')
      rw [one_smul, hfY]; exact one_pos
    refine lt_of_lt_of_le (hOo.measure_pos _ ⟨1, h1O⟩) (measure_mono fun g hg => ?_)
    exact (ENNReal.ofReal_pos.2 hg).ne'
  · refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hCfin
    have := hbound 1 h1N g
    rwa [rmulT_one] at this
  · have hev : ∀ᶠ T in 𝓝 (TI X u' hT), a T ∈ N := hac.preimage_mem_nhds (by rw [ha1]; exact hN)
    refine tendsto_lintegral_filter_of_dominated_convergence (C.indicator 1) ?_ ?_ hCfin.ne ?_
    · exact Eventually.of_forall fun T => ENNReal.measurable_ofReal.comp
        (f.continuous.comp (continuous_smul_left X _)).measurable
    · exact hev.mono fun T hT' => Eventually.of_forall fun g => hbound _ hT' g
    · refine Eventually.of_forall fun g => ?_
      exact (ENNReal.continuous_ofReal.comp (f.continuous.comp ((continuous_smul_tupI X g).comp
        (continuous_rmulT X (Y0 X u'))))).continuousAt.comp hac

theorem constTest_of_polar_proper (hP : PolarLoc) (hY : FrameIndependentAtInfinity) (hPr : ProperOrb) : ConstTest :=
  constTest_of_polar hP (pushCont_of hY hPr)

end PI.AprimeInfW
