import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Section
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]

def BcrisPlus.liftFracWitt (g : WittVector p k →+* R) :
    FractionRing (WittVector p k) →+* BcrisPlus p R :=
  fracWittLift p ((algebraMap (Acris p R) (BcrisPlus p R)).comp
    ((algebraMap (Ainf p R) (Acris p R)).comp (Ainf.liftWitt p g))) (BcrisPlus.isUnit_p p R)

variable {p}

@[simp] theorem BcrisPlus.liftFracWitt_algebraMap (g : WittVector p k →+* R) (a : WittVector p k) :
    BcrisPlus.liftFracWitt p g (algebraMap _ _ a) =
      algebraMap (Acris p R) _ (algebraMap (Ainf p R) _ (Ainf.liftWitt p g a)) :=
  fracWittLift_algebraMap p _ _ a

theorem BcrisPlus.map_liftFracWitt (e : R →+* S) (g : WittVector p k →+* R)
    (x : FractionRing (WittVector p k)) :
    BcrisPlus.map p e (BcrisPlus.liftFracWitt p g x) = BcrisPlus.liftFracWitt p (e.comp g) x :=
  RingHom.congr_fun (fracWitt_hom_ext
    (f := (BcrisPlus.map p e).comp (BcrisPlus.liftFracWitt p g))
    (g := BcrisPlus.liftFracWitt p (e.comp g)) (by simp [Ainf.map_liftWitt])) x

theorem fracWitt_frobenius_algebraMap (a : WittVector p k) :
    WittVector.FractionRing.frobenius p k (algebraMap _ _ a) =
      algebraMap _ _ (WittVector.frobenius a) := by
  rw [WittVector.FractionRing.frobenius, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

theorem BcrisPlus.frob_liftFracWitt (g : WittVector p k →+* R)
    (x : FractionRing (WittVector p k)) :
    BcrisPlus.frob p R (BcrisPlus.liftFracWitt p g x) =
      BcrisPlus.liftFracWitt p g (WittVector.FractionRing.frobenius p k x) :=
  RingHom.congr_fun (fracWitt_hom_ext
    (f := (BcrisPlus.frob p R).comp (BcrisPlus.liftFracWitt p g))
    (g := (BcrisPlus.liftFracWitt p g).comp (WittVector.FractionRing.frobenius p k).toRingHom)
    (by simp [Ainf.frob_liftWitt, fracWitt_frobenius_algebraMap])) x

theorem AinfInv.frob_liftFracWitt (g : WittVector p k →+* R)
    (x : FractionRing (WittVector p k)) :
    AinfInv.frob p R (AinfInv.liftFracWitt p g x) =
      AinfInv.liftFracWitt p g (WittVector.FractionRing.frobenius p k x) :=
  RingHom.congr_fun (fracWitt_hom_ext
    (f := (AinfInv.frob p R).comp (AinfInv.liftFracWitt p g))
    (g := (AinfInv.liftFracWitt p g).comp (WittVector.FractionRing.frobenius p k).toRingHom)
    (by simp [Ainf.frob_liftWitt, fracWitt_frobenius_algebraMap])) x

end Reformulated.AutPerF
