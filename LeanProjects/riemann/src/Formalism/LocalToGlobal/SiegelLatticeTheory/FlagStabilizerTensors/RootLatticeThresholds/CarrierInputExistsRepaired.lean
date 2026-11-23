import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInputExistsBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBJoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopPSD

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCMT2

theorem carrier_input_exists_repaired (hPA : Formalism.FourierDecayAlt.P5.ThmPActual)
    (hLEM : Formalism.FourierDecayAlt.MA.LemmaEModel) (hMP : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2)
    (hBB : Formalism.FourierDecayAlt.KB.BuiltBounds2) (Cb : ℝ) :
    ∃ C₆ Cc C₄ : ℝ, 0 < C₆ ∧ 1 ≤ C₄ ∧ ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
      (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
      (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
      (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (jn CA : ℝ)
      (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ),
      CarrierDataBound X u u' sc i0 i0' FdN FdN' νq jn CA G0 de de' l C₆ Cc Cb →
      CarrierInput X u u' sc i0 i0' FdN FdN' νq δ M C₄ jn CA G0 de de' l := by
  obtain ⟨C₆, Cc, C₄, hC6, hC4, hmain⟩ := Formalism.FourierDecayAlt.P.real_inputs_closed_model_place_two hPA Formalism.FourierDecayAlt.P.radial_module_form
    Formalism.FourierDecayAlt.P.positive_density_moderate_growth Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate Formalism.FourierDecayAlt.P.theorem_P_module_moderate_growth
    Formalism.FourierDecayAlt.P.radial_measure_is_haar hLEM Formalism.FourierDecayAlt.P.levels_of_built_setting Formalism.FourierDecayAlt.P.slices_finite_regularity_built hMP Formalism.FourierDecayAlt.P.top_positive_semidefinite
    hBB Cb
  refine ⟨C₆, Cc, C₄, hC6, hC4, fun D X u u' sc i0 i0' FdN FdN' νq δ M jn CA G0 de de' l hD => ?_⟩
  haveI : IsCMField D.host.E := instCMT2 D
  obtain ⟨Wp, Wq, i1, i2, i3, i4, i5, i6, S, p, f, χ, A₀, c, τ, Q, Qi, eP, eQ, hCA, hG, hde, hde', hl,
    hComp, hB, hSB, hc, hcut, hVt, hBF, hBase, hTop, hVJ, hE⟩ := hD
  letI := i1; letI := i2; letI := i3; letI := i4; letI := i5; letI := i6
  obtain ⟨L, j, lam, Cm, σ, hM, hRI⟩ := hmain D.host.E Wp Wq S p f χ A₀ c _
    (VtPt X u u' sc i0 i0' FdN FdN' νq) hB hSB hc hcut hVt
  refine ⟨Wp, Wq, i1, i2, i3, i4, i6, S, Formalism.FourierDecayAlt.KB.plT S p, f, χ, Formalism.FourierDecayAlt.KB.plν S p, Formalism.FourierDecayAlt.KB.plm S p,
    Formalism.FourierDecayAlt.KB.plTop S p, A₀, τ, Q, Qi, eP, eQ, hCA, hG, hde, hde', hl, hComp, isBuilt_of_builtPlace hB, hBF, hBase, hTop,
    hVJ, ?_⟩
  unfold Formalism.L2.SG.DataInst.dOf
  rw [← hE L j lam Cm σ hM]
  exact hRI _ _ _ _

end Formalism.L2.SG.Pf.CarrierT
