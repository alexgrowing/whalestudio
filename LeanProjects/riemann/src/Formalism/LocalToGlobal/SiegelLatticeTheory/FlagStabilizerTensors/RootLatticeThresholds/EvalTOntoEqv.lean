import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoPsi
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates Formalism.MainNotions.S
open Formalism.MainNotions.StandardLattice Matrix
open scoped InnerProductSpace ComplexConjugate ENNReal TensorProduct

namespace Formalism.L2.SG.EvalTOntoEqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.EvalTOntoExt Formalism.L2.SG.EvalTOntoPsi Classical

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)}
  {μ : Measure (GA D (D.sp.Y 0))} {c : ℝ} {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S}
  {U : ∀ v, X.B.H v ≃ₗᵢ⋆[ℂ] M.H (X.pl v)} {Φ : X.B.Hs →L[ℂ] L2X X}

def single (v' : NumberField.InfinitePlace X.B.I.F) (m : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)
    (hm : m ∈ UJset (X.B.I.ε v')) : X.B.I.Ginf :=
  Function.update 1 v' ⟨(Formalism.IndefR.SchurOrthogonalityAlt.isUnit_of_mem_UJ (X.B.I.ε v') hm).unit, hm⟩

end Formalism.L2.SG.EvalTOntoEqv

end
