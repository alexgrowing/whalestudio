import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomMain
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv
import Formalism.PeriodIntegrals.QuotSetU

set_option linter.unusedVariables false

open MeasureTheory

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge

theorem quotRightInv' (hI : PI.QuotInv) (hU : PI.QuotSetU) : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv := by
  intro k r z μG μS νq hz hT hG hS hq κ hκ F hF hFS
  obtain ⟨h1, h2, h3, h4, h5⟩ := hU k r z hz hT
  exact hI (2 * r + k + 1) _ _ μG μS νq ⟨h1, h2, h3, hG, hS, h4 μG hG, h5 μS hS, hq⟩ F hF hFS κ hκ

theorem quotRightInv_closed : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv := quotRightInv' quotient_invariant quotient_measure_unitary_group

theorem momNorm'_closed (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  momNorm'_of D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS hM1 hSm quotRightInv_closed Formalism.MainNotions.S.Pv.QuotUniq.quotLeftNorm

theorem momNorm'_closed_at (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : LowKOneAt D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  momNorm'_of_at D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS hM1 hSm quotRightInv_closed Formalism.MainNotions.S.Pv.QuotUniq.quotLeftNorm

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ)

def BesselSchurF' : Prop :=
  ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => BesselSchur' (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn

theorem momF'_of_schur (hBS : BesselSchurF' Fm Cg cb Cu cT CT C0) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomF' Fm Cg cb Cu cT CT C0 :=
  fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => momNorm'_closed _ _ _ _ _ _ _ _ _ _ _ h hM1 hSm) (hBS Cn)

theorem momF'_of_schur_at (hBS : BesselSchurF' Fm Cg cb Cu cT CT C0)
    (hM1 : ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => LowKOneAt (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomF' Fm Cg cb Cu cT CT C0 :=
  fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => momNorm'_closed_at _ _ _ _ _ _ _ _ _ _ _ h.1 h.2 hSm)
    ((hBS Cn).and (hM1 Cn))

end Fam

end Formalism.MainNotions.S.Pv.Mom
