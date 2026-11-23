import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.FactorialMulTruncLog
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open scoped Formalism.Per

namespace GlobalTheory.AdicMaps

open Formalism

noncomputable section

section Gen
variable {R S : Type} [CommRing R] [CommRing S]

def levMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (n : ℕ) :
    R ⧸ I ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f (Reformulated.AutPerF.pow_le_comap_pow hf n)

theorem levMap_mk (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (n : ℕ) (r : R) :
    levMap I J f hf n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (f r) := by
  first | exact @AdicLevelMap.Bridge.AdicMaps.levMap_mk | exact AdicLevelMap.Bridge.AdicMaps.levMap_mk .. | (intros; apply AdicLevelMap.Bridge.AdicMaps.levMap_mk <;> assumption)

theorem factorPow_evalₐ (I : Ideal R) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  first | exact @FactorPowerEval.Bridge.AdicMaps.factorPow_evalₐ | exact FactorPowerEval.Bridge.AdicMaps.factorPow_evalₐ .. | (intros; apply FactorPowerEval.Bridge.AdicMaps.factorPow_evalₐ <;> assumption)

theorem levMap_compat (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp ((levMap I J f hf n).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) =
    (levMap I J f hf m).comp (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m) := by
  first | exact @AdicLevelCompat.Bridge.AdicMaps.levMap_compat | exact AdicLevelCompat.Bridge.AdicMaps.levMap_compat .. | (intros; apply AdicLevelCompat.Bridge.AdicMaps.levMap_compat <;> assumption)

def adicMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  Reformulated.AutPerF.adicMap I J f hf

theorem evalₐ_adicMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (n : ℕ)
    (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (adicMap I J f hf x) = levMap I J f hf n (AdicCompletion.evalₐ I n x) := by
  first | exact @AdicEvaluationMap.Bridge.AdicMaps.evalₐ_adicMap | exact AdicEvaluationMap.Bridge.AdicMaps.evalₐ_adicMap .. | (intros; apply AdicEvaluationMap.Bridge.AdicMaps.evalₐ_adicMap <;> assumption)

theorem evalₐ_adicMap_mk (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (n : ℕ)
    (x : AdicCompletion I R) (r : R) (h : AdicCompletion.evalₐ I n x = Ideal.Quotient.mk _ r) :
    AdicCompletion.evalₐ J n (adicMap I J f hf x) = Ideal.Quotient.mk _ (f r) := by
  first | exact @AdicEvaluationMk.Bridge.AdicMaps.evalₐ_adicMap_mk | exact AdicEvaluationMk.Bridge.AdicMaps.evalₐ_adicMap_mk .. | (intros; apply AdicEvaluationMk.Bridge.AdicMaps.evalₐ_adicMap_mk <;> assumption)

theorem adicMap_alg (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (r : R) :
    adicMap I J f hf (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (f r) := by
  first | exact @AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg | exact AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg .. | (intros; apply AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg <;> assumption)

theorem span_le_comap (p : ℕ) (f : R →+* S) :
    Ideal.span {(p : R)} ≤ (Ideal.span {(p : S)}).comap f := by
  first | exact @AdicSpanLeComap.Bridge.AdicMaps.span_le_comap | exact AdicSpanLeComap.Bridge.AdicMaps.span_le_comap .. | (intros; apply AdicSpanLeComap.Bridge.AdicMaps.span_le_comap <;> assumption)

abbrev PHat (p : ℕ) (R : Type) [CommRing R] : Type := AdicCompletion (Ideal.span {(p : R)}) R

def padicMap (p : ℕ) (f : R →+* S) : PHat p R →+* PHat p S :=
  Reformulated.AutPerF.adicMap _ _ f (Reformulated.AutPerF.span_natCast_le_comap p f)

theorem padicMap_alg (p : ℕ) (f : R →+* S) (r : R) :
    padicMap p f (algebraMap R (PHat p R) r) = algebraMap S (PHat p S) (f r) := by
  first | exact @PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg | exact PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg .. | (intros; apply PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg <;> assumption)

end Gen

theorem exists_acris_completion (l : ℕ) [Fact l.Prime] :
    ∃ e : Per.Acris l ≃+* AdicCompletion (Ideal.span {(l : Per.Acris0 l)}) (Per.Acris0 l),
      ∀ s : Per.Acris0 l, e (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
        algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {(l : Per.Acris0 l)}) (Per.Acris0 l)) s := by
  first | exact @CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion | exact CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion .. | (intros; apply CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion <;> assumption)

theorem coeff_galois (l : ℕ) [Fact l.Prime] (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : Per.Fl l)
    (n : ℕ) (y : Per.OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) y) :
    PreTilt.coeff n (Per.σF g x) =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (Per.σO g y) := by
  first | exact @AdicCoeffGalois.Bridge.AdicMaps.coeff_galois | exact AdicCoeffGalois.Bridge.AdicMaps.coeff_galois .. | (intros; apply AdicCoeffGalois.Bridge.AdicMaps.coeff_galois <;> assumption)

end

end GlobalTheory.AdicMaps
