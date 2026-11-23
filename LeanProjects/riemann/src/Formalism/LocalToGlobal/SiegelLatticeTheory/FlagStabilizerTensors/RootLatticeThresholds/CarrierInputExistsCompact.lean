import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierPOfRepairedModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealInputsClosedCompactSupportOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityCompactSupport

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCMT2

end Formalism.L2.SG.Pf.CarrierT

open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.SpectralTiesReal

open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.RealObj

theorem carrierP_of_compact_model (hPA : P5.ThmPActualCpt) (hLEM : MA.LemmaEModel) (hMP : JCT.ModelPlaceBuilt2)
    (hBB : KB.BuiltBounds2Cpt) (Cb : ℝ) (hX : CarrierSideBoundPositive Cb) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨C₆, Cc, C₄, hC₆, hC₄, H⟩ :=
    Formalism.FourierDecayAlt.P.RealInputsCompactSupport.real_inputs_closed_compact_support_of hPA Formalism.FourierDecayAlt.P.radial_module_form
      Formalism.FourierDecayAlt.P.positive_density_compact_support Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate
      Formalism.FourierDecayAlt.P.theorem_P_module_compact_support Formalism.FourierDecayAlt.P.radial_measure_is_haar hLEM
      Formalism.FourierDecayAlt.P.levels_of_built_setting Formalism.FourierDecayAlt.P.slices_finite_regularity_built hMP
      Formalism.FourierDecayAlt.P.top_positive_semidefinite hBB Cb
  obtain ⟨CA₀, hX1⟩ := hX C₆ Cc hC₆
  refine ⟨C₄, CA₀, hC₄, ?_⟩
  intro CA hCA h1CA C0 CG CDel cT Cb' h1 h2 h3 h4 h5 h6
  obtain ⟨k0, hk⟩ := hX1 CA hCA h1CA C0 CG CDel cT Cb' h1 h2 h3 h4 h5 h6
  refine ⟨k0, ?_⟩
  intro Cg cb Cw cTf CT C0f hcb hcTf
  obtain ⟨C'₀, Cl₀, hC⟩ := hk Cg cb Cw cTf CT C0f hcb hcTf
  refine ⟨C'₀, Cl₀, ?_⟩
  intro C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hTies hu hk0 hHyp hpl hSz
    hi0 hPt hNu
  have hData := hC C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th vR Q hTies hu hk0 hHyp hpl hSz
    hi0 hPt hNu
  obtain ⟨Wp, Wq, i1, i2, i3, i4, i5, i6, S, p, f, χ, A₀, c, τ', Qm, Qim, eP, eQ,
    hCA', hG, hde, hde', hl, hComp, hBP, hSB, hc, hcut, hVt, hBX, hBase, hTop, hVJ, hjn⟩ := hData
  unfold CarrierFull
  refine ⟨Wp, Wq, i1, i2, i3, i4, i6, S, Formalism.FourierDecayAlt.KB.plT S p, f, Formalism.FourierDecayAlt.KB.plν S p,
    Formalism.FourierDecayAlt.KB.plm S p, τ', Qm, Qim, eP, eQ, hCA', hG, hde, hde', hl, hComp, hBase, hTop, hVJ, ?_⟩
  obtain ⟨L', j, lam, Cm, σ, hMod, hRI⟩ := H D.host.E Wp Wq S p f χ A₀ c _ _ hBP hSB hc hcut hVt
  rw [← hjn L' j lam Cm σ hMod]
  exact hRI _ _ _ _

end Formalism.L2.SG.SpectralTiesReal
