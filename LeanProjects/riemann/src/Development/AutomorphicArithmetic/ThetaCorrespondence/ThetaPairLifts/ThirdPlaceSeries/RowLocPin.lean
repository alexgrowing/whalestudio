import Formalism.LocalToGlobal.IndefiniteReal.TensCastR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S IsDedekindDomain NumberField
open scoped TensorProduct
namespace Formalism.IndefR.principalLevelFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
def RowLocPinAlt {V : HSp D} {Sp : D.what₂.Tau → SPar} (lp : Formalism.L2.LPTiedPlaceholder D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (PY : RowPsi V D.R.r)
    (M : Formalism.IndefR.Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (eFT : D.what₂.FT ≃ FTR θ PY M J χ e) : Prop :=
  _root_.Formalism.L2.RowLocTiedAlt D lp (Formalism.L2.Col.rowFrameOf D (OccRows θ PY M J χ e) eFT)
end Formalism.IndefR.principalLevelFrame
end
end
