import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SqChartCore

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ActMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (Z : TupI X),
    Measurable (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Z)

def FibOrbAt : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∀ T ∈ Ω₁, ∃ k : ENNReal,
      fibInf T = k • X.measG.μGinf.map (fun g => g • rmulT X (a T) (Y0 X u'))

def OrbCont : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∃ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) ∧
      PolId X u' μinf νinf a Ω₁ c

def JacOneC : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) →
      PolId X u' μinf νinf a Ω₂ c → c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹

theorem isOpen_ne_zero_top : IsOpen (({0}ᶜ ∩ {⊤}ᶜ : Set ENNReal)) :=
  isOpen_compl_singleton.inter isOpen_compl_singleton

theorem polar_local_of_orbit (hK : KPos) (h2 : OrbCont) (h4 : JacOneC) : PolarLoc := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω, a, hC⟩ := sqChart_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, c, hcc, hc⟩ := h2 X u' ψ hT μinf νinf fibInf hP Ω a hC
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  have hc0 : c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹ :=
    h4 X u' ψ hT μinf νinf fibInf hP Ω a hC Ω₁ hΩ₁ hΩ₁n c hcc hc
  have hne0 : c (TI X u' hT) ≠ 0 := by rw [hc0]; exact ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hneT : c (TI X u' hT) ≠ ⊤ := by rw [hc0]; exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK0).ne'
  have hN : c ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ) ∈ 𝓝 (TI X u' hT) :=
    hcc (isOpen_ne_zero_top.mem_nhds ⟨Set.mem_compl_singleton_iff.2 hne0, Set.mem_compl_singleton_iff.2 hneT⟩)
  refine ⟨Ω₁ ∩ c ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ), a, fun T => ((c T)⁻¹).toReal, inter_mem hΩ₁n hN, hC.2.1, hC.2.2.1,
    ?_, ?_, ?_⟩
  · show ((c (TI X u' hT))⁻¹).toReal = KVal X u'
    rw [hc0, inv_inv, ENNReal.toReal_ofReal hK0.le]
  · have ht : (c (TI X u' hT))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne0
    have hinv : ContinuousAt (fun T => (c T)⁻¹) (TI X u' hT) := ENNReal.tendsto_inv_iff.2 hcc
    exact ContinuousAt.comp (g := ENNReal.toReal) (f := fun T => (c T)⁻¹) (ENNReal.continuousAt_toReal ht) hinv
  · intro φ hφ S hS hSm
    rw [hc φ hφ S (hS.trans Set.inter_subset_left) hSm]
    refine setLIntegral_congr_fun hSm ?_
    intro T hTS
    have hT2 := (hS hTS).2
    have h0 : c T ≠ 0 := Set.mem_compl_singleton_iff.1 hT2.1
    show c T * _ = (ENNReal.ofReal ((c T)⁻¹).toReal)⁻¹ * _
    rw [ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 h0), inv_inv]

theorem orbCont_of (hG : GramMeas) (hA : ActMeas) (h1 : FibOrbAt) (h2 : PushCont) : OrbCont := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, hk⟩ := h1 X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨φ, hφc, hφm, hφs, hφU, hφ0, hIpos, hIfin, hIc⟩ := h2 X u' ψ hT μinf νinf fibInf hP a hC.2.1 hC.2.2.1
  have hfib := hP.2.2.2.2.2.2
  have hΦm : Measurable fun y => ENNReal.ofReal (φ y) := ENNReal.measurable_ofReal.comp hφm
  set I : HmI X → ENNReal := fun T =>
    ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a T) (Y0 X u'))) ∂X.measG.μGinf with hIdef
  set Nf : HmI X → ENNReal := fun T => ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf T) with hNdef
  have hI1 : I (TI X u' hT) = ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf := by
    simp only [hIdef]; rw [hC.2.1, rmulT_one]
  have hI0 : I (TI X u' hT) ≠ 0 := by rw [hI1]; exact hIpos.ne'
  have hIT : I (TI X u' hT) ≠ ⊤ := by rw [hI1]; exact hIfin.ne
  have hIN : I ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ) ∈ 𝓝 (TI X u' hT) :=
    hIc (isOpen_ne_zero_top.mem_nhds ⟨Set.mem_compl_singleton_iff.2 hI0, Set.mem_compl_singleton_iff.2 hIT⟩)

  have c3 := hfib.2.2 φ hφc hφs hφU
  have hNeq : Nf = fun T => ENNReal.ofReal (∫ v, φ v ∂(fibInf T)) := by
    funext T
    exact (ofReal_integral_eq_lintegral_ofReal (c3.1 T (Set.mem_univ _))
      (Eventually.of_forall fun y => hφ0 y)).symm
  have hNc : ContinuousAt Nf (TI X u' hT) := by
    rw [hNeq]
    exact (ENNReal.continuous_ofReal.comp (continuousOn_univ.1 c3.2)).continuousAt
  refine ⟨Ω₁ ∩ I ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ), Set.inter_subset_left.trans hΩ₁, inter_mem hΩ₁n hIN,
    fun T => Nf T / I T, ENNReal.Tendsto.div hNc (Or.inr hI0) hIc (Or.inl hIT), ?_⟩
  intro φ' hφ' S hS hSm
  have hGS := hG X S hSm
  have c2 := hfib.2.1 ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator φ')
    (hφ'.indicator hGS)
  rw [lintegral_indicator hGS, Measure.restrict_restrict hGS] at c2
  rw [c2]
  have inner : ∀ b, ∫⁻ v, (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator φ' v
      ∂(fibInf b) = S.indicator (fun T => ∫⁻ v, φ' v ∂(fibInf T)) b := by
    intro b
    have hae : ∀ᵐ y ∂(fibInf b), y ∈ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {Subtype.val b} ∩ IndI X :=
      ae_iff.2 (hfib.1 b)
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
      exact Set.indicator_of_mem (Set.mem_preimage.2 (show gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y ∈
        Subtype.val '' S from ⟨b, hb, hy1.symm⟩)) _
    · rw [Set.indicator_of_notMem hb]
      calc _ = ∫⁻ _, (0 : ENNReal) ∂(fibInf b) := by
              apply lintegral_congr_ae
              filter_upwards [hae] with y hy
              have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
              refine Set.indicator_of_notMem ?_ _
              rintro ⟨c, hc, hcy⟩
              have hcb : c = b := Subtype.val_injective (hcy.trans hy1)
              exact hb (hcb ▸ hc)
        _ = 0 := lintegral_zero
  simp_rw [inner]
  rw [lintegral_indicator hSm]
  refine setLIntegral_congr_fun hSm ?_
  intro T hTS
  obtain ⟨k, hkT⟩ := hk T (hS hTS).1
  have hIT2 := (hS hTS).2
  have h0 : I T ≠ 0 := Set.mem_compl_singleton_iff.1 hIT2.1
  have hTop : I T ≠ ⊤ := Set.mem_compl_singleton_iff.1 hIT2.2
  have hm := hA X (rmulT X (a T) (Y0 X u'))
  have e1 : ∀ ψ' : TupI X → ENNReal, Measurable ψ' →
      ∫⁻ v, ψ' v ∂(fibInf T) = k * ∫⁻ g, ψ' (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf := by
    intro ψ' hψ'
    rw [hkT, lintegral_smul_measure, lintegral_map hψ' hm, smul_eq_mul]
  have hNk : Nf T = k * I T := e1 _ hΦm
  show ∫⁻ v, φ' v ∂(fibInf T) = Nf T / I T * ∫⁻ g, φ' (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf
  rw [hNk, ENNReal.mul_div_cancel_right h0 hTop, e1 φ' hφ']

theorem polar_local_of_action (hK : KPos) (hG : GramMeas) (hA : ActMeas) (h1 : FibOrbAt) (h2 : PushCont) (h4 : JacOneC) :
    PolarLoc :=
  polar_local_of_orbit hK (orbCont_of hG hA h1 h2) h4

end PI.AprimeInfW
