import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol

noncomputable section

namespace Formalism.L2.SG.LocVol.LJP

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
open scoped TensorProduct

def DiagProp : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (v : PlX X),
    TFv X w v = Matrix.diagonal (fun i : Fin (D.R.rS + 1) =>
      if i = Fin.last D.R.rS then -((Tw w : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) else 0)

def HermProp : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (v : PlX X),
    TFv X w v ∈ HermR (Fv X.B.I.F v) X.B.I.cm.sig (D.R.rS + 1)

def IntProp : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (v : PlX X),
    TypAt X v → (gAt X v : ℤ) ∣ ((Tw u : ℤ) - Tw u') →
      ∀ i j, (TFv X u' v i j - TFv X u v i j) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ ∈ OEv (E := X.B.I.E) v

end Formalism.L2.SG.LocVol.LJP
