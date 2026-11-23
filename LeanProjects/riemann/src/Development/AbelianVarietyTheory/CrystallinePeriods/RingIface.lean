import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.FactorialMulTruncLog
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section
namespace GlobalTheory.RingIface
open Formalism Reformulated.AutPerF
open scoped Formalism.Per

namespace X
variable {l : ℕ} [Fact l.Prime]
theorem alg_mem_kerP {a : Per.Ainf l} (h : Per.θ l a = 0) : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
  first | exact @AlgebraMemThetaKernel.Bridge.alg_mem_kerP | exact AlgebraMemThetaKernel.Bridge.alg_mem_kerP .. | (intros; apply AlgebraMemThetaKernel.Bridge.alg_mem_kerP <;> assumption)

theorem dp (x : Per.Ainf l) (n : ℕ) (y : Per.AinfP l) (hx : Per.θ l x = 0)
    (h : ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n) : y ∈ Per.Acris0 l := by
  first | exact @DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 | exact DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 .. | (intros; apply DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 <;> assumption)

theorem le (S : Subalgebra (Per.Ainf l) (Per.AinfP l)) (h : ∀ x : Per.Ainf l, Per.θ l x = 0 → ∀ (n : ℕ) (y : Per.AinfP l),
    y ∈ Per.Acris0 l → ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n → y ∈ S) :
    Per.Acris0 l ≤ S := by
  first | exact @CrisZeroLeThird.Bridge.acris0_le_3 | exact CrisZeroLeThird.Bridge.acris0_le_3 .. | (intros; apply CrisZeroLeThird.Bridge.acris0_le_3 <;> assumption)

end X

variable (l : ℕ) [Fact l.Prime]

theorem phiA_teich (y : Per.Fl l) : Per.φA l (WittVector.teichmuller l y) = WittVector.teichmuller l (y ^ l) := by
  first | exact @FrobeniusTeichmuller.Bridge.phiA_teich | exact FrobeniusTeichmuller.Bridge.phiA_teich .. | (intros; apply FrobeniusTeichmuller.Bridge.phiA_teich <;> assumption)

theorem sigA_teich (g : Per.Gq l) (y : Per.Fl l) :
    Per.σA g (WittVector.teichmuller l y) = WittVector.teichmuller l (Per.σF g y) := by
  first | exact @TeichmullerAction.Bridge.sigA_teich | exact TeichmullerAction.Bridge.sigA_teich .. | (intros; apply TeichmullerAction.Bridge.sigA_teich <;> assumption)

theorem sigA_coeff (g : Per.Gq l) (w : Per.Ainf l) (n : ℕ) : (Per.σA g w).coeff n = Per.σF g (w.coeff n) := by
  first | exact @SigmaCoeffA.Bridge.sigA_coeff | exact SigmaCoeffA.Bridge.sigA_coeff .. | (intros; apply SigmaCoeffA.Bridge.sigA_coeff <;> assumption)

theorem sigO_coe (g : Per.Gq l) (y : Per.OC l) : ((Per.σO g y : Per.OC l) : ℂ_[l]) = Per.σC g (y : ℂ_[l]) := by
  first | exact @IntegralActionCoe.Bridge.sigO_coe | exact IntegralActionCoe.Bridge.sigO_coe .. | (intros; apply IntegralActionCoe.Bridge.sigO_coe <;> assumption)

theorem sigC_cont (g : Per.Gq l) : Continuous (Per.σC g) := by
  first | exact @ContinuousGalois.Bridge.sigC_cont | exact ContinuousGalois.Bridge.sigC_cont .. | (intros; apply ContinuousGalois.Bridge.sigC_cont <;> assumption)

theorem tower (x : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) x =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) := by
  first | exact @ScalarTowerAlt.Bridge.tower | exact ScalarTowerAlt.Bridge.tower .. | (intros; apply ScalarTowerAlt.Bridge.tower <;> assumption)

theorem sigD_alg (g : Per.Gq l) (b : Per.BdRp l) : Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) b) =
    algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g b) := by
  first | exact @DeRhamSigmaAlgebra.Bridge.sigD_alg | exact DeRhamSigmaAlgebra.Bridge.sigD_alg .. | (intros; apply DeRhamSigmaAlgebra.Bridge.sigD_alg <;> assumption)

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a := by
  first | exact @EvaluationAlgebra.Bridge.ev_alg | exact EvaluationAlgebra.Bridge.ev_alg .. | (intros; apply EvaluationAlgebra.Bridge.ev_alg <;> assumption)

theorem ev_ext (y y' : Per.BdRp l) (h : ∀ n, Per.ev l n y = Per.ev l n y') : y = y' := by
  first | exact @EvaluationExt.Bridge.ev_ext | exact EvaluationExt.Bridge.ev_ext .. | (intros; apply EvaluationExt.Bridge.ev_ext <;> assumption)

theorem phiA_coeff (w : Per.Ainf l) (n : ℕ) : (Per.φA l w).coeff n = w.coeff n ^ l := by
  first | exact @FrobeniusCoeffA.Bridge.phiA_coeff | exact FrobeniusCoeffA.Bridge.phiA_coeff .. | (intros; apply FrobeniusCoeffA.Bridge.phiA_coeff <;> assumption)

theorem fontaineTheta_algebraMap (a : Per.Ainf l) :
    Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = ((Per.θ l a : Per.OC l) : ℂ_[l]) := by
  first | exact @ThetaAlgebraMap.Bridge.fontaineTheta_algebraMap | exact ThetaAlgebraMap.Bridge.fontaineTheta_algebraMap .. | (intros; apply ThetaAlgebraMap.Bridge.fontaineTheta_algebraMap <;> assumption)

theorem alg_mem_kerP {a : Per.Ainf l} (h : Per.θ l a = 0) : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
  first | exact @AlgebraMemThetaKernel.Bridge.alg_mem_kerP | exact AlgebraMemThetaKernel.Bridge.alg_mem_kerP .. | (intros; apply AlgebraMemThetaKernel.Bridge.alg_mem_kerP <;> assumption)

theorem ev_surj (n : ℕ) : Function.Surjective (Per.ev l n) := by
  first | exact @EvaluationSurjective.Bridge.ev_surj | exact EvaluationSurjective.Bridge.ev_surj .. | (intros; apply EvaluationSurjective.Bridge.ev_surj <;> assumption)

theorem thetaD_alg (a : Per.AinfP l) : Per.θD l (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Per.θP l a := by
  first | exact @ThetaDeRhamAlgebra.Bridge.thetaD_alg | exact ThetaDeRhamAlgebra.Bridge.thetaD_alg .. | (intros; apply ThetaDeRhamAlgebra.Bridge.thetaD_alg <;> assumption)

theorem thetaD_of_mem_FilP {y : Per.BdRp l} (h : y ∈ Per.FilP l 1) : Per.θD l y = 0 := by
  first | exact @ThetaOfFiltration.Bridge.thetaD_of_mem_FilP | exact ThetaOfFiltration.Bridge.thetaD_of_mem_FilP .. | (intros; apply ThetaOfFiltration.Bridge.thetaD_of_mem_FilP <;> assumption)

theorem sigDp_alg (g : Per.Gq l) (a : Per.AinfP l) : Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
    algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) := by
  first | exact @DividedPowerAlgebraMap.Bridge.sigDp_alg | exact DividedPowerAlgebraMap.Bridge.sigDp_alg .. | (intros; apply DividedPowerAlgebraMap.Bridge.sigDp_alg <;> assumption)

theorem isUnit_of_generator {a : Per.AinfP l} (h : Per.kerP l = Ideal.span {a}) : IsUnit (Per.pD l a) := by
  first | exact @IsUnitOfGenerator.Bridge.isUnit_of_generator | exact IsUnitOfGenerator.Bridge.isUnit_of_generator .. | (intros; apply IsUnitOfGenerator.Bridge.isUnit_of_generator <;> assumption)

theorem exists_bdRp_equiv : ∃ e : Per.BdRp l ≃+* AdicCompletion (Per.kerP l) (Per.AinfP l),
    (∀ a, e (algebraMap (Per.AinfP l) (Per.BdRp l) a) = algebraMap _ _ a) ∧
      ∀ n y, AdicCompletion.evalₐ (Per.kerP l) n (e y) = Per.ev l n y := by
  first | exact @DeRhamPlusEquivExists.Bridge.exists_bdRp_equiv | exact DeRhamPlusEquivExists.Bridge.exists_bdRp_equiv .. | (intros; apply DeRhamPlusEquivExists.Bridge.exists_bdRp_equiv <;> assumption)

theorem bcris_ext {R : Type} [CommRing R] {f g : Per.Bcris l →+* R}
    (h : ∀ x, f (algebraMap (Per.Acris l) (Per.Bcris l) x) = g (algebraMap (Per.Acris l) (Per.Bcris l) x)) : f = g := by
  first | exact @PeriodRingExt.Bridge.bcris_ext | exact PeriodRingExt.Bridge.bcris_ext .. | (intros; apply PeriodRingExt.Bridge.bcris_ext <;> assumption) | exact @CrisHomExt.Bridge.CrisLoc.bcris_hom_ext | exact CrisHomExt.Bridge.CrisLoc.bcris_hom_ext .. | (intros; apply CrisHomExt.Bridge.CrisLoc.bcris_hom_ext <;> assumption)

theorem alg_mem_FilD_nat {n : ℕ} {z : Per.BdRp l} (h : z ∈ Per.FilP l n) :
    algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l (n : ℤ) := by
  first | exact @DeRhamFiltrationNat.Bridge.alg_mem_FilD_nat | exact DeRhamFiltrationNat.Bridge.alg_mem_FilD_nat .. | (intros; apply DeRhamFiltrationNat.Bridge.alg_mem_FilD_nat <;> assumption)

theorem exists_of_mem_FilD_nat {n : ℕ} {x : Per.BdR l} (h : x ∈ Per.FilD l (n : ℤ)) :
    ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  first | exact @FiltrationNatExists.Bridge.exists_of_mem_FilD_nat | exact FiltrationNatExists.Bridge.exists_of_mem_FilD_nat .. | (intros; apply FiltrationNatExists.Bridge.exists_of_mem_FilD_nat <;> assumption)

theorem zB_eq_aB_zA : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zB l z = Formalism.Per.aB l (Formalism.Per.zA l z) := by
  first | exact @GeneratorRelation.Bridge.zB_eq_aB_zA | exact GeneratorRelation.Bridge.zB_eq_aB_zA .. | (intros; apply GeneratorRelation.Bridge.zB_eq_aB_zA <;> assumption)

theorem mem_filtration_iff_mem_kerTheta_pow : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (y : Formalism.Per.BdRp l), y ∈ Formalism.Per.FilP l n ↔ Formalism.Per.ev l n y = 0 := by
  first | exact @DividedPowerFiltrationIff.Bridge.mem_filtration_iff_mem_kerTheta_pow | exact DividedPowerFiltrationIff.Bridge.mem_filtration_iff_mem_kerTheta_pow .. | (intros; apply DividedPowerFiltrationIff.Bridge.mem_filtration_iff_mem_kerTheta_pow <;> assumption)

theorem toC_alg : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.OC l), Formalism.Per.toC l (algebraMap (Formalism.Per.OC l) (Localization.Away ((l : ℕ) : Formalism.Per.OC l)) a) = (a : ℂ_[l]) := by
  first | exact @CrisToComplexAlgebra.Bridge.toC_alg | exact CrisToComplexAlgebra.Bridge.toC_alg .. | (intros; apply CrisToComplexAlgebra.Bridge.toC_alg <;> assumption)

theorem padicIntMap_eq_algebraMap_comp : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zP l z = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z) := by
  first | exact @GeneratorAlgebraRelation.Bridge.padicIntMap_eq_algebraMap_comp | exact GeneratorAlgebraRelation.Bridge.padicIntMap_eq_algebraMap_comp .. | (intros; apply GeneratorAlgebraRelation.Bridge.padicIntMap_eq_algebraMap_comp <;> assumption)

theorem dividedPower_mem_Acris0 : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Ainf l) (n : ℕ) (y : Formalism.Per.AinfP l), Formalism.Per.θ l x = 0 → ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ Formalism.Per.Acris0 l := by
  first | exact @DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 | exact DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 .. | (intros; apply DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 <;> assumption)

theorem Acris0_le_of_dividedPowers : ∀ (l : ℕ) [Fact l.Prime] (S : Subalgebra (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)), (∀ (x : Formalism.Per.Ainf l) (n : ℕ) (y : Formalism.Per.AinfP l), Formalism.Per.θ l x = 0 → ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ S) → Formalism.Per.Acris0 l ≤ S := by
  first | exact @CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers | exact CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers .. | (intros; apply CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers <;> assumption)

theorem aB_algebraMap_padicInt : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.aB l (algebraMap ℤ_[l] (Formalism.BasicNotions.Loc.Ainf l) z) = Formalism.Per.zB l z := by
  first | exact @GeneratorRelation.Bridge.zB_eq_aB_zA | exact GeneratorRelation.Bridge.zB_eq_aB_zA .. | (intros; apply GeneratorRelation.Bridge.zB_eq_aB_zA <;> assumption)

theorem zD_eq_alg : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) := by
  first | exact @DeRhamGeneratorAlgebra.Bridge.zD_eq_alg | exact DeRhamGeneratorAlgebra.Bridge.zD_eq_alg .. | (intros; apply DeRhamGeneratorAlgebra.Bridge.zD_eq_alg <;> assumption)

theorem aB_eq_alg : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l), Formalism.Per.aB l a = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) := by
  first | exact @PeriodMapApply.Bridge.aB_apply | exact PeriodMapApply.Bridge.aB_apply .. | (intros; apply PeriodMapApply.Bridge.aB_apply <;> assumption)

theorem aB_zl : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.aB l (algebraMap ℤ_[l] (Formalism.BasicNotions.Loc.Ainf l) z) = Formalism.Per.zB l z := by
  first | exact @GeneratorRelation.Bridge.zB_eq_aB_zA | exact GeneratorRelation.Bridge.zB_eq_aB_zA .. | (intros; apply GeneratorRelation.Bridge.zB_eq_aB_zA <;> assumption)

theorem zD_alg : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) := by
  first | exact @DeRhamGeneratorAlgebra.Bridge.zD_eq_alg | exact DeRhamGeneratorAlgebra.Bridge.zD_eq_alg .. | (intros; apply DeRhamGeneratorAlgebra.Bridge.zD_eq_alg <;> assumption)

theorem mem_Acris0_of_factorial_mul : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Ainf l), Formalism.Per.θ l x = 0 → ∀ (n : ℕ) (y : Formalism.Per.AinfP l), ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ Formalism.Per.Acris0 l := by
  first | exact @CrisZeroFactorialMul.Bridge.mem_Acris0_of_factorial_mul | exact CrisZeroFactorialMul.Bridge.mem_Acris0_of_factorial_mul .. | (intros; apply CrisZeroFactorialMul.Bridge.mem_Acris0_of_factorial_mul <;> assumption) | exact @DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 | exact DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 .. | (intros; apply DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 <;> assumption)

theorem aB_apply : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l), Formalism.Per.aB l a = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) := by
  first | exact @PeriodMapApply.Bridge.aB_apply | exact PeriodMapApply.Bridge.aB_apply .. | (intros; apply PeriodMapApply.Bridge.aB_apply <;> assumption)

theorem aB_alg : ∀ (l : ℕ) [Fact l.Prime] (w : Formalism.Per.Ainf l), Formalism.Per.aB l w = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) w) := by
  first | exact @PeriodMapApply.Bridge.aB_apply | exact PeriodMapApply.Bridge.aB_apply .. | (intros; apply PeriodMapApply.Bridge.aB_apply <;> assumption)

theorem aB_zA : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.aB l (Formalism.Per.zA l z) = Formalism.Per.zB l z := by
  first | exact @PeriodGeneratorImage.Bridge.aB_zA | exact PeriodGeneratorImage.Bridge.aB_zA .. | (intros; apply PeriodGeneratorImage.Bridge.aB_zA <;> assumption) | exact @GeneratorRelation.Bridge.zB_eq_aB_zA | exact GeneratorRelation.Bridge.zB_eq_aB_zA .. | (intros; apply GeneratorRelation.Bridge.zB_eq_aB_zA <;> assumption)

theorem pD_eq_alg : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.AinfP l), Formalism.Per.pD l a = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) a) := by
  first | exact @DividedPowerApply.Bridge.pD_apply | exact DividedPowerApply.Bridge.pD_apply .. | (intros; apply DividedPowerApply.Bridge.pD_apply <;> assumption)

theorem alg_mem_FilD_zero : ∀ (l : ℕ) [Fact l.Prime] (y : Formalism.Per.BdRp l), algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) y ∈ Formalism.Per.FilD l 0 := by
  first | exact @DeRhamFiltrationZero.Bridge.alg_mem_FilD_zero | exact DeRhamFiltrationZero.Bridge.alg_mem_FilD_zero .. | (intros; apply DeRhamFiltrationZero.Bridge.alg_mem_FilD_zero <;> assumption) | exact @DeRhamFiltrationNat.Bridge.alg_mem_FilD_nat | exact DeRhamFiltrationNat.Bridge.alg_mem_FilD_nat .. | (intros; apply DeRhamFiltrationNat.Bridge.alg_mem_FilD_nat <;> assumption)

theorem zB_alg : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zB l z = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.zA l z)) := by
  first | exact @CrisGeneratorAlgebra.Bridge.zB_alg | exact CrisGeneratorAlgebra.Bridge.zB_alg .. | (intros; apply CrisGeneratorAlgebra.Bridge.zB_alg <;> assumption) | exact @GeneratorRelation.Bridge.zB_eq_aB_zA | exact GeneratorRelation.Bridge.zB_eq_aB_zA .. | (intros; apply GeneratorRelation.Bridge.zB_eq_aB_zA <;> assumption)

theorem acris0_le : ∀ (l : ℕ) [Fact l.Prime] (S : Subalgebra (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)), (∀ x : Formalism.Per.Ainf l, Formalism.Per.θ l x = 0 → ∀ (n : ℕ) (y : Formalism.Per.AinfP l), ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ S) → Formalism.Per.Acris0 l ≤ S := by
  first | exact @CrisZeroLeAlt.Bridge.acris0_le | exact CrisZeroLeAlt.Bridge.acris0_le .. | (intros; apply CrisZeroLeAlt.Bridge.acris0_le <;> assumption) | exact @CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers | exact CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers .. | (intros; apply CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers <;> assumption)

theorem acris0_le_3 : ∀ (l : ℕ) [Fact l.Prime] (S : Subalgebra (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)), (∀ x : Formalism.Per.Ainf l, Formalism.Per.θ l x = 0 → ∀ (n : ℕ) (y : Formalism.Per.AinfP l), y ∈ Formalism.Per.Acris0 l → ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ S) → Formalism.Per.Acris0 l ≤ S := by
  first | exact @CrisZeroLeThird.Bridge.acris0_le_3 | exact CrisZeroLeThird.Bridge.acris0_le_3 .. | (intros; apply CrisZeroLeThird.Bridge.acris0_le_3 <;> assumption) | exact @CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers | exact CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers .. | (intros; apply CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers <;> assumption)

theorem dividedPower_mem : ∀ (l : ℕ) [Fact l.Prime] (m : Formalism.Per.Ainf l) (j : ℕ) (y : Formalism.Per.AinfP l), Formalism.Per.θ l m = 0 → ((j.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) m ^ j → y ∈ Formalism.Per.Acris0 l := by
  first | exact @DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 | exact DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 .. | (intros; apply DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 <;> assumption)

theorem ev_sigDp : ∀ (l : ℕ) [Fact l.Prime] (g : Formalism.Per.Gq l) (n : ℕ) (y : Formalism.Per.BdRp l) (a : Formalism.Per.AinfP l), Formalism.Per.ev l n y = Ideal.Quotient.mk _ a → Formalism.Per.ev l n (Formalism.Per.σDp g y) = Ideal.Quotient.mk _ (Formalism.Per.extP (Formalism.Per.σA g) a) := by
  first | exact @EvaluationDividedPower.Bridge.ev_sigDp | exact EvaluationDividedPower.Bridge.ev_sigDp .. | (intros; apply EvaluationDividedPower.Bridge.ev_sigDp <;> assumption)

end GlobalTheory.RingIface
