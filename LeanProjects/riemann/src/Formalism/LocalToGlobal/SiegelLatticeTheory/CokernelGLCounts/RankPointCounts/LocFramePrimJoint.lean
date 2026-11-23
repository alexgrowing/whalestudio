import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.PeriodIntegrals.LocFramePrim

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting
open scoped TensorProduct Classical

namespace ChkLocFramePrim

example {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (w : D.what₂.Word) (v : PlX X) :
    PI.LocFramePrim.IsPrim v (LamX X)
      (PI.LocFramePrim.locF v (PI.LocFramePrim.ratTup (PI.LocFramePrim.Fv X.B.I.F v) (F0 (frameOf X w)))) ↔
    IsPrim v (LamX X) (locF v (ratTup (Fv X.B.I.F v) (F0 (frameOf X w)))) := Iff.rfl

theorem primX_of (hS : PI.LocFramePrim.Statement) {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (w : D.what₂.Word)
    (Lb : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E))
    (hFG : X.B.I.L.FG)
    (hsplit : X.B.I.L =
      PI.LocFramePrim.latSpan (fun a : Fin D.R.rS => PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ))))
          (frameOf X w).e ⊔ Lb ⊔
        PI.LocFramePrim.latSpan (fun a : Fin D.R.rS => (PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ))))⁻¹)
          (frameOf X w).f)
    (hind : LinearIndependent X.B.I.E (Fin.append (frameOf X w).e (frameOf X w).f))
    (hdir : ∀ y ∈ Lb, y ∈ Submodule.span X.B.I.E (Set.range (frameOf X w).e ∪ Set.range (frameOf X w).f) → y = 0)
    (hz : (frameOf X w).z ∈ Lb)
    (hzp : ∀ c : X.B.I.E, c • (frameOf X w).z ∈ Lb → ∃ o : 𝓞 X.B.I.E, (o : X.B.I.E) = c) :
    PrimX X w := fun v =>
  hS X.B.I.F X.B.I.E v X.B.I.n D.R.rS X.B.I.L Lb (frameOf X w).e (frameOf X w).f (frameOf X w).z
    hFG hsplit hind hdir hz hzp

end ChkLocFramePrim
