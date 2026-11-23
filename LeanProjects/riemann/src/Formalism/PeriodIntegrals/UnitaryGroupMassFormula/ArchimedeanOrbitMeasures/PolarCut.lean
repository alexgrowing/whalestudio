import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstCut

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def IsChart {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (Ω : Set (HmI X)) (a : HmI X → MfI X) : Prop :=
  Ω ∈ 𝓝 (TI X u' hT) ∧ a (TI X u' hT) = 1 ∧ ContinuousAt a (TI X u' hT) ∧
    ∀ T ∈ Ω, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _)

def PolId {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (μinf : Measure (TupI X)) (νinf : Measure (HmI X))
    (a : HmI X → MfI X) (Ω : Set (HmI X)) (c : HmI X → ENNReal) : Prop :=
  ∀ φ : TupI X → ENNReal, Measurable φ → ∀ S ⊆ Ω, MeasurableSet S →
    ∫⁻ y in gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S) ∩ IndI X, φ y ∂μinf =
      ∫⁻ T in S, c T * ∫⁻ g, φ (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf ∂νinf

def SqChart : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a

def OrbAll : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∃ c : HmI X → ENNReal, PolId X u' μinf νinf a Ω₁ c

def ScaleAll : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ J : HmI X → ℝ, J (TI X u' hT) = 1 ∧ ContinuousAt J (TI X u' hT) ∧
      ∀ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) → ∀ c, PolId X u' μinf νinf a Ω₁ c →
        ∃ c₀ : ENNReal, ∃ Ω₂ ⊆ Ω₁, Ω₂ ∈ 𝓝 (TI X u' hT) ∧
          ∀ᵐ T ∂(νinf.restrict Ω₂), c T = c₀ * ENNReal.ofReal (J T)

def JacOne : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∀ J : HmI X → ℝ, J (TI X u' hT) = 1 → ContinuousAt J (TI X u' hT) →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c₀ : ENNReal,
      PolId X u' μinf νinf a Ω₂ (fun T => c₀ * ENNReal.ofReal (J T)) → c₀ = (ENNReal.ofReal (KVal X u'))⁻¹

theorem polarLoc_of (hK : KPos) (h1 : SqChart) (h2 : OrbAll) (h3 : ScaleAll) (h4 : JacOne) : PolarLoc := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω, a, hC⟩ := h1 X u' ψ hT μinf νinf fibInf hP
  obtain ⟨J, hJ1, hJc, hJ⟩ := h3 X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, c, hc⟩ := h2 X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨c₀, Ω₂, hΩ₂, hΩ₂n, hae⟩ := hJ Ω₁ hΩ₁ hΩ₁n c hc
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP

  have hid : PolId X u' μinf νinf a Ω₂ (fun T => c₀ * ENNReal.ofReal (J T)) := by
    intro φ hφ S hS hSm
    rw [hc φ hφ S (hS.trans hΩ₂) hSm]
    refine lintegral_congr_ae ?_
    have hae' : ∀ᵐ T ∂(νinf.restrict S), c T = c₀ * ENNReal.ofReal (J T) :=
      ae_restrict_of_ae_restrict_of_subset hS hae
    filter_upwards [hae'] with T hT'
    rw [hT']
  have hc₀ : c₀ = (ENNReal.ofReal (KVal X u'))⁻¹ :=
    h4 X u' ψ hT μinf νinf fibInf hP Ω a hC J hJ1 hJc Ω₂ (hΩ₂.trans hΩ₁) hΩ₂n c₀ hid
  have hJpos : {T | 0 < J T} ∈ 𝓝 (TI X u' hT) := hJc (Ioi_mem_nhds (by rw [hJ1]; exact one_pos))
  refine ⟨Ω₂ ∩ {T | 0 < J T}, a, fun T => KVal X u' / J T, inter_mem hΩ₂n hJpos, hC.2.1, hC.2.2.1,
    by simp [hJ1], ?_, ?_⟩
  · exact continuousAt_const.div hJc (by rw [hJ1]; exact one_ne_zero)
  · intro φ hφ S hS hSm
    rw [hid φ hφ S (hS.trans Set.inter_subset_left) hSm]
    refine setLIntegral_congr_fun hSm ?_
    intro T hTS
    have hJT : 0 < J T := (hS hTS).2
    have e : (ENNReal.ofReal (KVal X u' / J T))⁻¹ = (ENNReal.ofReal (KVal X u'))⁻¹ * ENNReal.ofReal (J T) := by
      rw [ENNReal.ofReal_div_of_pos hJT, ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top)
        (Or.inl (ENNReal.ofReal_pos.2 hJT).ne'), div_eq_mul_inv, mul_comm]
    simp only
    rw [e, hc₀]

end PI.AprimeInfW
