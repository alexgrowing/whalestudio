import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalToGlobal.LatticeGeometry.Inhabited
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo NumberField IsDedekindDomain

namespace GlobalTheory

def provisionalPadPkg (D : D7) (N j : ℕ) (hj : j ≤ N) (Comp : Type)
    (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) :
    PadPkg D N j Comp jC ngJunk where
  loc := fun p => junkLocalData D N j p
  ex := fun p => exJunk D N j p
  locB := fun p hp => junkLocB D N j p hp
  pbKF := fun _ _ k => Empty.elim k
  levIn := fun _ => True
  Xg := Empty
  bc := fun _ Z => Z.elim
  DivG := fun Z => Z.elim
  effD := @fun Z _ => Z.elim
  noVertD := @fun Z _ => Z.elim
  posBdD := @fun Z _ => Z.elim
  ampleOnAbelianBase := fun Z _ _ => Z.elim
  Met := Empty
  nefFibM := fun M => M.elim
  ampleGen := fun M => M.elim
  limRA := fun M => M.elim
  Mp := fun _ _ => PUnit
  md := fun p _ la _ => trivialAdmissibleModel D p (jC p la) N j hj
  CurveM := fun _ _ _ => Empty
  degM := fun _ _ _ c => c.elim
  htMdl := fun _ _ => PUnit.unit
  Pt := Empty
  compPt := fun y => y.elim
  phiDR := fun _ y => y.elim
  phiMod := fun _ y => y.elim
  phiFr := fun _ y => y.elim
  phiFr_unram := fun _ y => y.elim
  normDetT := fun _ _ y => y.elim
  normDetH := fun _ _ y => y.elim
  htDetT := fun _ _ _ => 0
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl

theorem nonempty_provisionalPadPkg :
    ∀ D : D7, ∃ ng : NgPkg, ∀ (N j : ℕ) (Comp : Type) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
      j ≤ N → Nonempty (PadPkg D N j Comp jC ng) :=
  fun D => ⟨ngJunk, fun N j Comp jC hj => ⟨provisionalPadPkg D N j hj Comp jC⟩⟩

end GlobalTheory
