import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesEqUnionThreeParts

noncomputable section

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Guard (K : Ctx) (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt) : Prop :=
  K.Over B.toPre ∧ KPx B f ∧ Forced K B T ∧ Pinned K B f T w ∧ GrpTrue Z.N f ∧ R3.GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) ∧
    R3.Holds z.R z.F

def idxPrimes (K : Ctx) (P : Pre) (f : Top.Fr P) (F F₀ : IntermediateField ℚ ℂ) : Set ℕ :=
  {p | ∃ (B : Base) (f' : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f' T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt), B.toPre = P ∧ HEq f' f ∧ B.KsC = F ∧ B.fixedCoefficientFieldInComplex = F₀ ∧ Guard K B f' T w Z hX Wt z ∧
      ∃ v ∈ z.IwasawaPlaceIndex ∪ z.W1jw, B.places.resChar v = p}

def forcedContentSupportPrimes (K : Ctx) (P : Pre) : Finset ℕ :=
  {P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

end
