import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action

noncomputable section

open Ideal

namespace UpperTheory.Ring.Comp

open Reformulated.AutPerF

abbrev Fl (l : ℕ) [Fact (Nat.Prime l)] : Type := Tilt l (PadicComplexInt l)

abbrev Ainf (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.Ainf l (PadicComplexInt l)

abbrev AinfP (l : ℕ) [Fact (Nat.Prime l)] : Type := AinfInv l (PadicComplexInt l)

abbrev BdRp (l : ℕ) [Fact (Nat.Prime l)] : Type := BdRPlus l (PadicComplexInt l)

abbrev BdR (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.BdR l (PadicComplexInt l)

abbrev Acris0 (l : ℕ) [Fact (Nat.Prime l)] : Subalgebra (Ainf l) (AinfP l) := acrisZero l (PadicComplexInt l)

abbrev Acris (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.Acris l (PadicComplexInt l)

abbrev Bcris (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.Bcris l (PadicComplexInt l)

abbrev Gq (l : ℕ) [Fact (Nat.Prime l)] : Type := PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l

def pcMap (l : ℕ) {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    AdicCompletion (span {(l : A)}) A →+* AdicCompletion (span {(l : B)}) B :=
  adicMap _ _ f (span_natCast_le_comap l f)

def zP (l : ℕ) [Fact (Nat.Prime l)] : ℤ_[l] →+* AinfP l := algebraMap ℤ_[l] (AinfP l)

def θP (l : ℕ) [Fact (Nat.Prime l)] : AinfP l →+* ℂ_[l] :=
  (IsUnitBall.awayEquiv (PadicComplexInt l) l).toRingEquiv.toRingHom.comp (AinfInv.theta l (PadicComplexInt l))

def pD (l : ℕ) [Fact (Nat.Prime l)] : AinfP l →+* BdR l :=
  (algebraMap (BdRp l) (BdR l)).comp (algebraMap (AinfP l) (BdRp l))

def zD (l : ℕ) [Fact (Nat.Prime l)] : ℤ_[l] →+* BdR l := (pD l).comp (zP l)

def aB (l : ℕ) [Fact (Nat.Prime l)] : Ainf l →+* Bcris l :=
  (algebraMap (Acris l) (Bcris l)).comp (algebraMap (Ainf l) (Acris l))

def a0B (l : ℕ) [Fact (Nat.Prime l)] : Acris0 l →+* Bcris l :=
  (algebraMap (Acris l) (Bcris l)).comp (algebraMap (AcrisZero l (PadicComplexInt l)) (Acris l))

def zB (l : ℕ) [Fact (Nat.Prime l)] : ℤ_[l] →+* Bcris l :=
  (algebraMap (Acris l) (Bcris l)).comp (algebraMap ℤ_[l] (Acris l))

def σD {l : ℕ} [Fact (Nat.Prime l)] (g : Gq l) : BdR l →+* BdR l :=
  MulSemiringAction.toRingHom (Gq l) (BdR l) g

end UpperTheory.Ring.Comp
