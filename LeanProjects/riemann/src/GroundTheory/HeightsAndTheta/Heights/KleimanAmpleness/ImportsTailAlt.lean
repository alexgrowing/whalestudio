import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftIntNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W → ∀ β : K → ℤ,
      intNum F (segreLift ι F W) ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg β] = intNum F W ![β]

theorem SegreLiftIntNum.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

example (h : SegreLiftIntNum.Statement) := h ℚ Unit (fun _ => Fin 2) ⊥ SegreLiftIntNum.hyps 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
