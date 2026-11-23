import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.CrystallineRing.Acris0

noncomputable section

namespace Formalism.Per

open Reformulated.AutPerF

section General
variable {R S : Type} [CommRing R] [CommRing S]
def compMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (h : I ≤ J.comap f) : AdicCompletion I R →+* AdicCompletion J S := adicMap I J f h
end General

section Cp
abbrev Qb (p : ℕ) [Fact p.Prime] : Type := PadicAlgCl p
abbrev Gq (p : ℕ) [Fact p.Prime] : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p
abbrev OC (p : ℕ) [Fact p.Prime] : Type := ↥(PadicComplexInt p)
variable {p : ℕ} [Fact p.Prime]
def σC (g : Gq p) : ℂ_[p] →+* ℂ_[p] := MulSemiringAction.toRingHom (Gq p) ℂ_[p] g
def σO (g : Gq p) : OC p →+* OC p := MulSemiringAction.toRingHom (Gq p) (OC p) g
end Cp

section Explicit
variable (l : ℕ) [Fact l.Prime]
scoped instance instFactNotIsUnitOCCast : Fact (¬ IsUnit ((l : ℕ) : OC l)) := inferInstance
scoped instance instIsAdicCompleteOCSpanSingletonSetCast : IsAdicComplete (Ideal.span {((l : ℕ) : OC l)}) (OC l) := inferInstance
abbrev Fl : Type := Tilt l (OC l)
abbrev Ainf : Type := Reformulated.AutPerF.Ainf l (OC l)
abbrev θ : Ainf l →+* OC l := WittVector.fontaineTheta (OC l) l
def φA : Ainf l →+* Ainf l := Ainf.frob l (OC l)
def zA : ℤ_[l] →+* Ainf l := Ainf.ofPadicInt l (OC l)
def AinfP : Type := AinfInv l (OC l)
instance instCommRingAinfP : CommRing (AinfP l) := inferInstanceAs (CommRing (AinfInv l (OC l)))
instance instAlgebraAinfAinfP : Algebra (Ainf l) (AinfP l) := inferInstanceAs (Algebra (Ainf l) (AinfInv l (OC l)))
instance instAwayAinfCastAinfP : IsLocalization.Away ((l : ℕ) : Ainf l) (AinfP l) :=
  inferInstanceAs (IsLocalization.Away ((l : ℕ) : Ainf l) (AinfInv l (OC l)))
def zP : ℤ_[l] →+* AinfP l := UpperTheory.Ring.Comp.zP l
def toC : Localization.Away ((l : ℕ) : OC l) →+* ℂ_[l] := (IsUnitBall.awayEquiv (PadicComplexInt l) l).toRingEquiv.toRingHom
def θP : AinfP l →+* ℂ_[l] := UpperTheory.Ring.Comp.θP l
def kerP : Ideal (AinfP l) := AinfInv.kerTheta l (OC l)
def BdRp : Type := BdRPlus l (OC l)
instance instCommRingBdRp : CommRing (BdRp l) := inferInstanceAs (CommRing (BdRPlus l (OC l)))
instance instAlgebraAinfPBdRp : Algebra (AinfP l) (BdRp l) := inferInstanceAs (Algebra (AinfInv l (OC l)) (BdRPlus l (OC l)))
def ev (n : ℕ) : BdRp l →+* AinfP l ⧸ kerP l ^ n := BdRPlus.eval l (OC l) n
def FilP (n : ℕ) : Ideal (BdRp l) := BdRPlus.fil l (OC l) n
def θD : BdRp l →+* ℂ_[l] := BdRPlus.thetaC l (PadicComplexInt l)
def BdR : Type := Reformulated.AutPerF.BdR l (OC l)
instance instCommRingBdR : CommRing (BdR l) := inferInstanceAs (CommRing (Reformulated.AutPerF.BdR l (OC l)))
instance instAlgebraBdRpBdR : Algebra (BdRp l) (BdR l) := inferInstanceAs (Algebra (BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l)))
instance instIsFractionRingBdR : IsFractionRing (BdRp l) (BdR l) :=
  inferInstanceAs (IsFractionRing (BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l)))
def pD : AinfP l →+* BdR l := UpperTheory.Ring.Comp.pD l
def zD : ℤ_[l] →+* BdR l := UpperTheory.Ring.Comp.zD l
def FilD (a : ℤ) : Submodule (BdRp l) (BdR l) := BdR.fil l (OC l) a
def Acris0 : Subalgebra (Ainf l) (AinfP l) := acrisZero l (OC l)
def Acris : Type := Reformulated.AutPerF.Acris l (OC l)
instance instCommRingAcris : CommRing (Acris l) := inferInstanceAs (CommRing (Reformulated.AutPerF.Acris l (OC l)))
instance instAlgebraAcris0Acris : Algebra ↥(Acris0 l) (Acris l) :=
  inferInstanceAs (Algebra (AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l)))
instance instAlgebraAinfAcris : Algebra (Ainf l) (Acris l) := inferInstanceAs (Algebra (Ainf l) (Reformulated.AutPerF.Acris l (OC l)))
def Bcris : Type := Reformulated.AutPerF.Bcris l (OC l)
instance instCommRingBcris : CommRing (Bcris l) := inferInstanceAs (CommRing (Reformulated.AutPerF.Bcris l (OC l)))
instance instAlgebraAcrisBcris : Algebra (Acris l) (Bcris l) :=
  inferInstanceAs (Algebra (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)))
def aB : Ainf l →+* Bcris l := UpperTheory.Ring.Comp.aB l
def a0B : ↥(Acris0 l) →+* Bcris l := UpperTheory.Ring.Comp.a0B l
def zB : ℤ_[l] →+* Bcris l := UpperTheory.Ring.Comp.zB l
def φB : Bcris l →+* Bcris l := Bcris.frob l (OC l)
structure IsCrisDR (f : Bcris l →+* BdR l) : Prop where
  on0 : ∀ a : Acris0 l, f (a0B l a) = pD l (a : AinfP l)
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Acris l, ∃ (y : BdRp l) (a : Ainf l),
    f (algebraMap (Acris l) (Bcris l) x) = algebraMap (BdRp l) (BdR l) y ∧
      ev l n (((l : ℕ) : BdRp l) ^ N * y) = Ideal.Quotient.mk _ (algebraMap (Ainf l) (AinfP l) a)
end Explicit

section Implicit
variable {l : ℕ} [Fact l.Prime]
abbrev tm (x : Fl l) : Ainf l := WittVector.teichmuller l x
def σF (g : Gq l) : Fl l →+* Fl l := Tilt.map l (σO g)
def σA (g : Gq l) : Ainf l →+* Ainf l := Ainf.map l (σO g)
def extP (f : Ainf l →+* Ainf l) : AinfP l →+* AinfP l := AinfInv.extend l f
def σDp (g : Gq l) : BdRp l →+* BdRp l := BdRPlus.map l (σO g)
def σD (g : Gq l) : BdR l →+* BdR l := UpperTheory.Ring.Comp.σD g
def σB (g : Gq l) : Bcris l →+* Bcris l := Bcris.map l (σO g) (MulAction.injective g)
def IsLog (l : ℕ) [Fact l.Prime] (e : Fl l) (y : BdRp l) : Prop :=
  ∃ h, y = BdRPlus.log (algebraMap (Ainf l) (BdRPlus l (OC l)) (tm e)) h
end Implicit

end Formalism.Per
