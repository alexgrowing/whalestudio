import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.FactorialMulTruncLog
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsExtensionU
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
import Development.AutomorphicArithmetic.TeichmullerLogarithm.LogQuot
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism
open scoped Formalism.Per

namespace GlobalTheory.CrisLoc

variable (l : ℕ) [Fact l.Prime]

theorem exists_root_ne_one : ∃ e : Per.Fl l, e.untilt = 1 ∧ e ≠ 1 := by
  first | exact @CrisRootNeOne.Bridge.CrisLoc.exists_root_ne_one | exact CrisRootNeOne.Bridge.CrisLoc.exists_root_ne_one .. | (intros; apply CrisRootNeOne.Bridge.CrisLoc.exists_root_ne_one <;> assumption)

theorem bcris_away (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsLocalization.Away (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1)) (Per.Bcris l) := by
  first | exact @CrisAway.Bridge.CrisLoc.bcris_away | exact CrisAway.Bridge.CrisLoc.bcris_away .. | (intros; apply CrisAway.Bridge.CrisLoc.bcris_away <;> assumption)

theorem bdR_away (b : Per.AinfP l) (hb : Per.kerP l = Ideal.span {b}) :
    IsLocalization.Away (algebraMap (Per.AinfP l) (Per.BdRp l) b) (Per.BdR l) := by
  first | exact @DeRhamAway.Bridge.CrisLoc.bdR_away | exact DeRhamAway.Bridge.CrisLoc.bdR_away .. | (intros; apply DeRhamAway.Bridge.CrisLoc.bdR_away <;> assumption)

theorem mem_fil_neg (b : Per.AinfP l) (hb : Per.kerP l = Ideal.span {b}) (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l (-(n : ℤ)) ↔ ∃ y : Per.BdRp l,
      x * algebraMap (Per.BdRp l) (Per.BdR l) (algebraMap (Per.AinfP l) (Per.BdRp l) b) ^ n =
        algebraMap (Per.BdRp l) (Per.BdR l) y := by
  first | exact @FiltrationNeg.Bridge.CrisLoc.mem_fil_neg | exact FiltrationNeg.Bridge.CrisLoc.mem_fil_neg .. | (intros; apply FiltrationNeg.Bridge.CrisLoc.mem_fil_neg <;> assumption)

theorem unit_of_root (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1))) := by
  first | exact @UnitOfRootAlt.Bridge.CrisLoc.unit_of_root | exact UnitOfRootAlt.Bridge.CrisLoc.unit_of_root .. | (intros; apply UnitOfRootAlt.Bridge.CrisLoc.unit_of_root <;> assumption)

theorem unit_of_root_aB (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (Per.aB l (Per.tm e - 1)) := by
  first | exact @UnitOfRootLog.Bridge.CrisLoc.unit_of_root_aB | exact UnitOfRootLog.Bridge.CrisLoc.unit_of_root_aB .. | (intros; apply UnitOfRootLog.Bridge.CrisLoc.unit_of_root_aB <;> assumption)

theorem bcris_hom_ext {R : Type*} [CommRing R] {f g : Per.Bcris l →+* R}
    (h : ∀ x : Per.Acris l, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  CrisHomExtUnit.Bridge.CrisLoc.bcris_hom_ext_u l h

theorem exists_mul_pow_eq (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) (b : Per.Bcris l) :
    ∃ (n : ℕ) (x : Per.Acris l), b * algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1)) ^ n = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  first | exact @MulPowEq.Bridge.CrisLoc.exists_mul_pow_eq | exact MulPowEq.Bridge.CrisLoc.exists_mul_pow_eq .. | (intros; apply MulPowEq.Bridge.CrisLoc.exists_mul_pow_eq <;> assumption)

theorem exists_pow_mul_eq_zero (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) {x : Per.Acris l}
    (hx : algebraMap (Per.Acris l) (Per.Bcris l) x = 0) :
    ∃ n : ℕ, algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ^ n * x = 0 := by
  first | exact @PowMulEqZero.Bridge.CrisLoc.exists_pow_mul_eq_zero | exact PowMulEqZero.Bridge.CrisLoc.exists_pow_mul_eq_zero .. | (intros; apply PowMulEqZero.Bridge.CrisLoc.exists_pow_mul_eq_zero <;> assumption)

theorem exists_extension (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) {R : Type*} [CommRing R]
    (g : Per.Acris l →+* R) (hg : IsUnit (g (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1)))) :
    ∃ F : Per.Bcris l →+* R, ∀ x : Per.Acris l, F (algebraMap _ _ x) = g x :=
  CrisExtensionUnit.Bridge.CrisLoc.exists_extension_u l e he hne g hg

theorem bdR_hom_ext {R : Type*} [CommRing R] {f g : Per.BdR l →+* R}
    (h : ∀ x : Per.BdRp l, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  DeRhamHomExtUnit.Bridge.CrisLoc.bdR_hom_ext_u l h

theorem constantCoeff_root_ne_zero (e : Per.Fl l) (hne : e ≠ 1) :
    WittVector.constantCoeff (Per.tm e - 1 : Per.Ainf l) ≠ 0 := by
  first | exact @RootConstantCoeffNeZero.Bridge.CrisLoc.constantCoeff_root_ne_zero | exact RootConstantCoeffNeZero.Bridge.CrisLoc.constantCoeff_root_ne_zero .. | (intros; apply RootConstantCoeffNeZero.Bridge.CrisLoc.constantCoeff_root_ne_zero <;> assumption)

end GlobalTheory.CrisLoc
