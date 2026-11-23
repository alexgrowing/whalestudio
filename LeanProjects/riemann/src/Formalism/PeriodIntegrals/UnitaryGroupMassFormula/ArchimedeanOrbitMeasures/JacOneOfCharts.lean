import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacGlue

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def UnimodInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (f : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal) (h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J),
      ∫⁻ g, f (g * h) ∂X.measG.μGinf = ∫⁻ g, f g ∂X.measG.μGinf

def WittNear : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a Ω' a₂, IsChart X u' hT Ω a → IsChart X u' hT Ω' a₂ →
    ∀ T ∈ Ω ∩ Ω', IsUnit (a₂ T) → ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')

def GoodChartEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω' a₂, IsChart X u' hT Ω' a₂ ∧ GoodP X u' hT μinf νinf a₂

theorem jacOne_of_charts (hK : KPos) (hU : UnimodInf) (hW : WittNear) (hG : GoodChartEx) : JacOne := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC J hJ1 hJc Ω₂ hΩ₂ hΩ₂n c₀ hid
  obtain ⟨Ω', a₂, hC₂, hgood⟩ := hG X u' ψ hT μinf νinf fibInf hP
  have hev : ∀ᶠ T in 𝓝 (TI X u' hT), ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u') := by
    obtain ⟨ι, _, κ, -, η, _, eT, eH, cμ, cν, Ψ', U, -, -, -, -, -, -, -, -, hev0, -⟩ := hgood
    filter_upwards [hev0, hC.1, hC₂.1] with T h1 h2 h3
    exact hW X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T ⟨h2, h3⟩ h1.1
  set Ω₃ := Ω₂ ∩ Ω' ∩ {T | ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')} with hΩ₃
  have hΩ₃n : Ω₃ ∈ 𝓝 (TI X u' hT) := inter_mem (inter_mem hΩ₂n hC₂.1) hev
  have hid₂ : PolId X u' μinf νinf a₂ Ω₃ (fun T => c₀ * ENNReal.ofReal (J T)) := by
    intro φ hφ S hS hSm
    rw [hid φ hφ S (hS.trans (Set.inter_subset_left.trans Set.inter_subset_left)) hSm]
    refine setLIntegral_congr_fun hSm (fun T hT' => ?_)
    obtain ⟨h, eh⟩ := (hS hT').2
    rw [eh]
    congr 1
    have e : ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
        φ (g • h • rmulT X (a₂ T) (Y0 X u')) = (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) (g * h) := by
      intro g; simp only [mul_smul]
    simp_rw [e]
    exact hU X u' ψ hT μinf νinf fibInf hP (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) h
  exact jacOneGood hK X u' ψ hT μinf νinf fibInf hP Ω' a₂ hC₂ hgood J hJ1 hJc Ω₃
    (Set.inter_subset_left.trans Set.inter_subset_right) hΩ₃n c₀ hid₂

end PI.AprimeInfW
