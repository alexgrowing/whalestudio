import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

def plainPairNumber.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d N : ℕ)
    (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O) (m : ℕ) (G : MvPolynomial (Fin N) ℤ),
    G.IsHomogeneous m → ∀ Q : List (K → ℤ), Q.length + m = d + 1 →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
                                (Fin.append x Q.get) (Fin.append x' Q.get) (Fin.append f fun _ => 1)
                                (Fin.append g fun _ => 1)
                                (rename (Fin.castAdd Q.length) G * rename (Fin.natAdd N) (∏ j : Fin Q.length, X j)) =
        pairNum P x x' f g
          (fun i => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) Q

end GroundTheory.Heights₂.Heights.NumbersDVR
