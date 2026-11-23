import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.StatBKInIso
import Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.PropLocGKOf

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.T2
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc RealLatG fracBilinear)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

theorem bkInIso : StatBKInIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D i X _ _ k hk _ _ _ _ HfV HfV'
    hK hO hF hD hinv hinvF hc hBK
  refine ⟨ReciprocityTheory.ChartRestriction.T2.finite_H1_of_iso hK hO i hD, hBK, ?_, ?_, ?_, ?_, rfl⟩
  · intro f
    exact ReciprocityTheory.ChartRestriction.T2.tate_rational_frac hK hO hF i hD hinvF f
  · intro a t
    change D.pr ((LinearEquiv.ofInjective k hk).symm ((LinearEquiv.ofInjective k hk) (D.q a))) t = _
    rw [LinearEquiv.symm_apply_apply]
    exact ReciprocityTheory.ChartRestriction.T2.tate_compat_iso D hc a t
  · intro x hx
    have h0 : (LinearEquiv.ofInjective k hk).symm x = 0 :=
      ReciprocityTheory.ChartRestriction.T2.tate_integral_iso hK hO hF i hD hinv _ hx
    have := congrArg (LinearEquiv.ofInjective k hk) h0
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  · rw [← Submodule.map_comp, ← Submodule.map_comp]
    rfl

theorem kRowInj : StatKRowInj := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ G _ _ D M _ _ ρM u hu
  exact (ReciprocityTheory.ChartRestriction.T2.transportH1_injective (MulEquiv.refl G) u ρM D.ρA hu).comp
    (ReciprocityTheory.ChartRestriction.T2.continuousH1_toH1_injective D.ρA)

theorem bkInRow : StatBKInRow := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ Dw _ D i u hu
    _ _ _ _ HfV HfV' hK hO hF hD hinv hinvF hc hBK
  have hk := kRowInj O VT VT' Dw D M _ u hu
  exact ⟨hk, bkInIso p K O VT VT' Dw D i _ _ hk HfV HfV' hK hO hF hD hinv hinvF hc hBK⟩

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
