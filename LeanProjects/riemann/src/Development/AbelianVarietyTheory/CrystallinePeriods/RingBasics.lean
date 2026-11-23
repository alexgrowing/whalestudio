import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.FactorialMulTruncLog
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

open Formalism
open scoped Formalism.Per

namespace GlobalTheory.RingBasics

section Field
variable {p : ℕ} [Fact p.Prime]

theorem norm_eq_val (x : ℂ_[p]) : ‖x‖ = ((Valued.v x : NNReal) : ℝ) := by
  first | exact @NormEqValuation.Bridge.RingBasics.norm_eq_val | exact NormEqValuation.Bridge.RingBasics.norm_eq_val .. | (intros; apply NormEqValuation.Bridge.RingBasics.norm_eq_val <;> assumption)

theorem mem_OC (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  first | exact @IntegralComplexMem.Bridge.RingBasics.mem_OC | exact IntegralComplexMem.Bridge.RingBasics.mem_OC .. | (intros; apply IntegralComplexMem.Bridge.RingBasics.mem_OC <;> assumption)

theorem p_ne_zero : ((p : ℕ) : ℂ_[p]) ≠ 0 := by
  first | exact @PrimeNeZero.Bridge.RingBasics.p_ne_zero | exact PrimeNeZero.Bridge.RingBasics.p_ne_zero .. | (intros; apply PrimeNeZero.Bridge.RingBasics.p_ne_zero <;> assumption)

theorem norm_p_lt : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  first | exact @NormPrimeLtOne.Bridge.RingBasics.norm_p_lt | exact NormPrimeLtOne.Bridge.RingBasics.norm_p_lt .. | (intros; apply NormPrimeLtOne.Bridge.RingBasics.norm_p_lt <;> assumption)

theorem norm_gal (g : Per.Gq p) (x : Per.Qb p) : ‖g x‖ = ‖x‖ := by
  first | exact @GaloisNormAlt.Bridge.RingBasics.norm_gal | exact GaloisNormAlt.Bridge.RingBasics.norm_gal .. | (intros; apply GaloisNormAlt.Bridge.RingBasics.norm_gal <;> assumption)

theorem mem_span_pow_OC (n : ℕ) (x : Per.OC p) :
    x ∈ (Ideal.span {((p : ℕ) : Per.OC p)}) ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ n := by
  first | exact @SpanPowerIntegral.Bridge.RingBasics.mem_span_pow_OC | exact SpanPowerIntegral.Bridge.RingBasics.mem_span_pow_OC .. | (intros; apply SpanPowerIntegral.Bridge.RingBasics.mem_span_pow_OC <;> assumption)

theorem σC_coe (g : Per.Gq p) (x : Per.Qb p) :
    Per.σC g (x : ℂ_[p]) = ((g x : Per.Qb p) : ℂ_[p]) := by
  first | exact @FrobeniusComplexCoe.Bridge.RingBasics.σC_coe | exact FrobeniusComplexCoe.Bridge.RingBasics.σC_coe .. | (intros; apply FrobeniusComplexCoe.Bridge.RingBasics.σC_coe <;> assumption)

theorem norm_σC (g : Per.Gq p) (x : ℂ_[p]) : ‖Per.σC g x‖ = ‖x‖ := by
  first | exact @NormGaloisComplex.Bridge.RingBasics.norm_σC | exact NormGaloisComplex.Bridge.RingBasics.norm_σC .. | (intros; apply NormGaloisComplex.Bridge.RingBasics.norm_σC <;> assumption)

theorem σC_one (x : ℂ_[p]) : Per.σC (1 : Per.Gq p) x = x := by
  first | exact @FrobeniusComplexOne.Bridge.RingBasics.σC_one | exact FrobeniusComplexOne.Bridge.RingBasics.σC_one .. | (intros; apply FrobeniusComplexOne.Bridge.RingBasics.σC_one <;> assumption)

theorem σC_mul (g h : Per.Gq p) (x : ℂ_[p]) : Per.σC (g * h) x = Per.σC g (Per.σC h x) := by
  first | exact @FrobeniusMulComplex.Bridge.RingBasics.σC_mul | exact FrobeniusMulComplex.Bridge.RingBasics.σC_mul .. | (intros; apply FrobeniusMulComplex.Bridge.RingBasics.σC_mul <;> assumption)

theorem σF_one (x : Per.Fl p) : Per.σF (1 : Per.Gq p) x = x := by
  first | exact @FrobeniusTiltOne.Bridge.RingBasics.σF_one | exact FrobeniusTiltOne.Bridge.RingBasics.σF_one .. | (intros; apply FrobeniusTiltOne.Bridge.RingBasics.σF_one <;> assumption)

theorem σF_mul (g h : Per.Gq p) (x : Per.Fl p) : Per.σF (g * h) x = Per.σF g (Per.σF h x) := by
  first | exact @FrobeniusTiltMul.Bridge.RingBasics.σF_mul | exact FrobeniusTiltMul.Bridge.RingBasics.σF_mul .. | (intros; apply FrobeniusTiltMul.Bridge.RingBasics.σF_mul <;> assumption)

theorem untilt_σF (g : Per.Gq p) (x : Per.Fl p) : (Per.σF g x).untilt = Per.σO g x.untilt := by
  first | exact @UntiltFrobenius.Bridge.RingBasics.untilt_σF | exact UntiltFrobenius.Bridge.RingBasics.untilt_σF .. | (intros; apply UntiltFrobenius.Bridge.RingBasics.untilt_σF <;> assumption)

theorem σA_one (x : Per.Ainf p) : Per.σA (1 : Per.Gq p) x = x := by
  first | exact @FrobeniusOneA.Bridge.RingBasics.σA_one | exact FrobeniusOneA.Bridge.RingBasics.σA_one .. | (intros; apply FrobeniusOneA.Bridge.RingBasics.σA_one <;> assumption)

theorem σA_mul (g h : Per.Gq p) (x : Per.Ainf p) : Per.σA (g * h) x = Per.σA g (Per.σA h x) := by
  first | exact @FrobeniusMulA.Bridge.RingBasics.σA_mul | exact FrobeniusMulA.Bridge.RingBasics.σA_mul .. | (intros; apply FrobeniusMulA.Bridge.RingBasics.σA_mul <;> assumption)

theorem θ_σA (g : Per.Gq p) (x : Per.Ainf p) : Per.θ p (Per.σA g x) = Per.σO g (Per.θ p x) := by
  first | exact @ThetaFrobeniusA.Bridge.RingBasics.θ_σA | exact ThetaFrobeniusA.Bridge.RingBasics.θ_σA .. | (intros; apply ThetaFrobeniusA.Bridge.RingBasics.θ_σA <;> assumption)

theorem awayMap_algebraMap₂ (f : Per.Ainf p →+* Per.Ainf p) (x : Per.Ainf p) :
    Per.extP f (algebraMap (Per.Ainf p) (Per.AinfP p) x) = algebraMap (Per.Ainf p) (Per.AinfP p) (f x) := by
  first | exact @ExtensionAlgebra.Bridge.RingBasics.awayMap_algebraMap₂ | exact ExtensionAlgebra.Bridge.RingBasics.awayMap_algebraMap₂ .. | (intros; apply ExtensionAlgebra.Bridge.RingBasics.awayMap_algebraMap₂ <;> assumption)

theorem extP_inv (g : Per.Gq p) (x : Per.AinfP p) :
    Per.extP (Per.σA g) (Per.extP (Per.σA g⁻¹) x) = x := by
  first | exact @ExtendedInverse.Bridge.RingBasics.extP_inv | exact ExtendedInverse.Bridge.RingBasics.extP_inv .. | (intros; apply ExtendedInverse.Bridge.RingBasics.extP_inv <;> assumption)

theorem ker_σ (g : Per.Gq p) : Per.kerP p ≤ Ideal.comap (Per.extP (Per.σA g)) (Per.kerP p) := by
  first | exact @FrobeniusKernel.Bridge.RingBasics.ker_σ | exact FrobeniusKernel.Bridge.RingBasics.ker_σ .. | (intros; apply FrobeniusKernel.Bridge.RingBasics.ker_σ <;> assumption)

end Field

section Explicit
variable (l : ℕ) [Fact l.Prime]

theorem exists_pow_div_factorial (n : ℕ) :
    ∃ c : ℤ_[l], ((n.factorial : ℕ) : ℤ_[l]) * c = ((l : ℕ) : ℤ_[l]) ^ n := by
  first | exact @PowDivFactorialAlt.Bridge.RingBasics.exists_pow_div_factorial | exact PowDivFactorialAlt.Bridge.RingBasics.exists_pow_div_factorial .. | (intros; apply PowDivFactorialAlt.Bridge.RingBasics.exists_pow_div_factorial <;> assumption)

theorem φA_apply (x : Per.Ainf l) : Per.φA l x = WittVector.frobenius x := by
  first | exact @FrobeniusApplyA.Bridge.RingBasics.φA_apply | exact FrobeniusApplyA.Bridge.RingBasics.φA_apply .. | (intros; apply FrobeniusApplyA.Bridge.RingBasics.φA_apply <;> assumption)

theorem frob_lift (x : Per.Ainf l) : ∃ z : Per.Ainf l, Per.φA l x = x ^ l + (l : Per.Ainf l) * z := by
  first | exact @WittFrobeniusLift.Bridge.RingBasics.frob_lift | exact WittFrobeniusLift.Bridge.RingBasics.frob_lift .. | (intros; apply WittFrobeniusLift.Bridge.RingBasics.frob_lift <;> assumption)

theorem isUnit_l : IsUnit ((l : ℕ) : Per.AinfP l) := by
  first | exact @PrimeIsUnit.Bridge.RingBasics.isUnit_l | exact PrimeIsUnit.Bridge.RingBasics.isUnit_l .. | (intros; apply PrimeIsUnit.Bridge.RingBasics.isUnit_l <;> assumption)

theorem isUnit_nat (n : ℕ) (hn : n ≠ 0) : IsUnit ((n : ℕ) : Per.AinfP l) := by
  first | exact @NatIsUnit.Bridge.RingBasics.isUnit_nat | exact NatIsUnit.Bridge.RingBasics.isUnit_nat .. | (intros; apply NatIsUnit.Bridge.RingBasics.isUnit_nat <;> assumption)

theorem fontaineTheta_eq_zero_of_mem_ker (x : Per.AinfP l) (hx : x ∈ Per.kerP l ^ 1) : Per.θP l x = 0 := by
  first | exact @ThetaKernel.Bridge.RingBasics.fontaineTheta_eq_zero_of_mem_ker | exact ThetaKernel.Bridge.RingBasics.fontaineTheta_eq_zero_of_mem_ker .. | (intros; apply ThetaKernel.Bridge.RingBasics.fontaineTheta_eq_zero_of_mem_ker <;> assumption)

end Explicit

end GlobalTheory.RingBasics
