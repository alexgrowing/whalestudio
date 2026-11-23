import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.WeilFolding
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSympl
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EFinSmulEqOfFinPart
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Bes

variable {A T : HSp D} {ι : A.V →ₗ[D.host.E] T.V} (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A T ι)
  (P : Matrix (Fin d.ρ) (Fin T.rank) D.host.E)

def aCo (n : GA D T) (i : Fin d.ρ) : Fin d.ρ → AE D :=
  (P.map (incA D)).mulVec ((subOne T n).mulVec (ratV fun k => d.e k i))

def bCo (n : GA D T) : Fin d.ρ → AE D := (P.map (incA D)).mulVec ((subOne T n).mulVec (ratV d.z))

def CoOK (n : GA D T) : Prop :=
  (∀ i, (subOne T n).mulVec (ratV fun k => d.e k i) = (d.e.map (incA D)).mulVec (aCo d P n i)) ∧
    (subOne T n).mulVec (ratV d.z) = (d.e.map (incA D)).mulVec (bCo d P n)

def bcF (n : GA D T) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D)
    ((∑ i : Fin d.ρ, ∑ j : Fin d.ρ, if j.1 = i.1 + 1 then incA D (d.c i) * aCo d P n j i else 0) +
      ∑ i : Fin d.ρ, if i.1 + 1 = d.ρ then incA D (d.c i) * bCo d P n i else 0))

variable {d P}

end Bes

end Formalism.IndefR.Mi

end
