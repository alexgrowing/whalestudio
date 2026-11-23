import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.CompPiVLocGSame

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)

def SngSurj : Prop :=
  ∀ (I : AutInst) (p : HeightOneSpectrum (𝓞 I.F)) (k : HA (Fv I.F p) I.cm.sig I.J),
    k ∈ Kv I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) p →
    ∃ h : HA (Af I.F) I.cm.sig I.J, h ∈ Kf I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) ∧
      piV I p h = k ∧ ∀ v : HeightOneSpectrum (𝓞 I.F), v ≠ p → piV I v h = 1

end PI.MassDataKppVolLemmas
