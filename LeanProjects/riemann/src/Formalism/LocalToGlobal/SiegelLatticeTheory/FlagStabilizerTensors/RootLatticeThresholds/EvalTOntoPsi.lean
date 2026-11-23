import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoExt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.AutoReg
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.IndefiniteReal.RankZerothComponentEq

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.EvalTOntoPsi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.EvalTOntoExt

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)}
  {μ : Measure (GA D (D.sp.Y 0))} {c : ℝ}

section Pull

variable (hιs : Measurable ι.symm) (hι : Measurable ι) (hc : 0 < c)
  (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ) (hH : μ.IsHaarMeasure)
include hιs hι hc hmap hH

end Pull

section P

open Classical

variable {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} (U : ∀ v, X.B.H v ≃ₗᵢ⋆[ℂ] M.H (X.pl v))

def P (v : M.Vec) : X.B.Hs := X.B.tens fun v' => (U v').symm (v (X.pl v'))

end P

section Psi

open Classical

def psi {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} (U : ∀ v, X.B.H v ≃ₗᵢ⋆[ℂ] M.H (X.pl v))
    (Φ : X.B.Hs →L[ℂ] L2X X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (v : M.Vec)
    (h : GA D (D.sp.Y 0)) : ℂ :=
  star (ext0 X (Φ (P U v)) (ι (h * t⁻¹)))

variable {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} {U : ∀ v, X.B.H v ≃ₗᵢ⋆[ℂ] M.H (X.pl v)}
  {Φ : X.B.Hs →L[ℂ] L2X X}

variable (hιs : Measurable ι.symm) (hι : Measurable ι) (hc : 0 < c)
  (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ) (hH : μ.IsHaarMeasure)
include hιs hι hc hmap hH

end Psi

end Formalism.L2.SG.EvalTOntoPsi

end
