import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefGenericDVRSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreFibreIdeal.Statement : Prop :=
  ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (F : Type) [Field F] (φ : O →+* F)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω),
    segreRels ι F ⊆ ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) : Set _) ∧
    (mIdealOver O y).map (MvPolynomial.map φ) ≤
      ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ)).comap (segreIncl ι F) ∧
    ∀ W : Ideal (MRing ι F), (mIdealOver O y).map (MvPolynomial.map φ) ≤ W →
      (mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) ≤ segreLift ι F W

example (h : SegreFibreIdeal.Statement) :=
  h exO exΩ (IsLocalRing.ResidueField exO) (IsLocalRing.residue exO) Unit (fun _ => Fin (1 + 1))
    (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (Kleiman.lineX exF))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
