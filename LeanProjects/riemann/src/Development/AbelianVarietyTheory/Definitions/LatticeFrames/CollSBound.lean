import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt

noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Deg

def CollS {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : Prop :=
  (Y.tO u u).pairAbs ((Y.tO u u).big (Y.tO u u).nzSet) ≤
    (Real.sqrt ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)))⁻¹ ^ (D.R.k * D.R.f) * ddC X Y u u +
      Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) * duC X Y u

def CollSBound : Prop := Free CollS
end GlobalTheory.Core.Deg
