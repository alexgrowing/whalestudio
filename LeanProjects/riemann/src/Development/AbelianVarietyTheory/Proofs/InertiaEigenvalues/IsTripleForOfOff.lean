import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne

noncomputable section

namespace GlobalTheory.TripTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms
open Formalism.L2.Host (HChar CharFrame ValLL0 embLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.Triple
open GlobalTheory.EigTie
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW GaloisReps)
open GlobalTheory.LiftLeaf (CommG)
open GlobalTheory.SupLaw (OffRange)
open GlobalTheory.TwistAbove (twGL)

def SigAllAt (D : D7) (i : D.ntw.Tw) : Prop :=
  ∀ j b (x : D.nexp.Fm i j b) (ev : ℕ → PlE D.host → FractionRing (D.ntw.O i)), x ≠ 0 →
    MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) (D.nexp.eAlg i b) x = x →
    (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i → D.nexp.hkF i j b k P x = ev k P • x) →
    ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P →
      P ∉ D.ntw.S0 i → algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) = ev k P

def MeetsP0 (D : D7) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
  ∀ W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b), W ≠ ⊥ → GStable D.nexp i j b W →
    (∀ x ∈ W, eG D.nexp i j b x = x) → W ⊓ Fm0 D.nexp i j b ≠ ⊥

variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* Gab D.host.E D.nd.Om}

end GlobalTheory.TripTie

end
