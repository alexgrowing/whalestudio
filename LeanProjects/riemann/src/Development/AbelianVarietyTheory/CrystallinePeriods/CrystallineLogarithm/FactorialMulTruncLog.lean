import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.PadicField
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
namespace LogUniqueAlt
section
structure IsCrisDR (l : ℕ) [Fact l.Prime] (f : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) : Prop where
  on0 : ∀ a : ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)), f (((algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))).comp (algebraMap ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)))) a) = ((algebraMap (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))).comp (algebraMap (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)))) (a : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ∃ (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))),
    f (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) y ∧
      Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n (((l : ℕ) : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ^ N * y) = Ideal.Quotient.mk _ (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a)
def IsLog (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) : Prop :=
  ∃ h, y = Reformulated.AutPerF.BdRPlus.log (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (WittVector.teichmuller l e)) h

theorem Bridge.CrisIncl.log_unique : ∀ (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (he : PreTilt.untilt e = 1) (y y' : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (h : IsLog l e y) (h' : IsLog l e y'), y = y' := by
  intro l _ e _ y y' h h'
  obtain ⟨_, hy⟩ := h
  obtain ⟨_, hy'⟩ := h'
  exact hy.trans hy'.symm

end
end LogUniqueAlt
namespace CrisInclusionPeriod
section
structure IsCrisDR (l : ℕ) [Fact l.Prime] (f : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) : Prop where
  on0 : ∀ a : ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)), f (((algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))).comp (algebraMap ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)))) a) = ((algebraMap (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))).comp (algebraMap (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)))) (a : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ∃ (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))),
    f (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) y ∧
      Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n (((l : ℕ) : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ^ N * y) = Ideal.Quotient.mk _ (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a)
def IsLog (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) : Prop :=
  ∃ h, y = Reformulated.AutPerF.BdRPlus.log (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (WittVector.teichmuller l e)) h

theorem Bridge.CrisIncl.incl_aB : ∀ (l : ℕ) [Fact l.Prime] (ι : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) (h : IsCrisDR l ι) (a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))), ι (((algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))).comp (algebraMap (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)))) a) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) (algebraMap ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a)) := by
  intro l _ ι h a
  exact h.on0 (algebraMap (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l)) ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)) a)

end
end CrisInclusionPeriod
namespace FactorialMulEvaluation
section
structure IsCrisDR (l : ℕ) [Fact l.Prime] (f : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) : Prop where
  on0 : ∀ a : ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)), f (((algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))).comp (algebraMap ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)))) a) = ((algebraMap (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))).comp (algebraMap (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)))) (a : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ∃ (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))),
    f (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) y ∧
      Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n (((l : ℕ) : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ^ N * y) = Ideal.Quotient.mk _ (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a)
def IsLog (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) : Prop :=
  ∃ h, y = Reformulated.AutPerF.BdRPlus.log (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (WittVector.teichmuller l e)) h

namespace Bridge.CrisIncl.FactorialMulEvaluationLemmas

open Reformulated.AutPerF

theorem factorial_mul_truncLog {B : Type*} [CommRing B] [Algebra ℚ B] (n : ℕ) (x : B) :
    ((n.factorial : ℕ) : B) * truncLog n x =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : B) * x ^ (k + 1) := by
  rw [truncLog, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  obtain ⟨c, hc⟩ : (k + 1) ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) hk'
  rw [hc, Nat.mul_div_cancel_left c (Nat.succ_pos k), Algebra.smul_def, ← mul_assoc]
  congr 1
  have e2 : ((-1 : B)) ^ k = algebraMap ℚ B ((-1) ^ k) := by simp
  rw [e2, ← map_natCast (algebraMap ℚ B), ← map_natCast (algebraMap ℚ B) c, ← map_mul, ← map_mul]
  congr 1
  push_cast
  field_simp

theorem general {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [Fact ¬IsUnit (p : R)]
    [IsAdicComplete (Ideal.span {(p : R)}) R] (u : Ainf p R)
    (hu : BdRPlus.theta p R (algebraMap (Ainf p R) (BdRPlus p R) u) = 1) (n : ℕ) :
    ((n.factorial : ℕ) : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) *
      BdRPlus.eval p R n (BdRPlus.log (algebraMap (Ainf p R) (BdRPlus p R) u) hu) =
    Ideal.Quotient.mk _ (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : AinfInv p R) *
      (algebraMap (Ainf p R) (AinfInv p R) (u - 1)) ^ (k + 1)) := by
  have e : algebraMap (Ainf p R) (BdRPlus p R) u - 1 =
      algebraMap (AinfInv p R) (BdRPlus p R) (algebraMap (Ainf p R) (AinfInv p R) (u - 1)) := by
    rw [← IsScalarTower.algebraMap_apply, map_sub, map_one]
  rw [BdRPlus.eval_log, factorial_mul_truncLog, e, BdRPlus.eval_algebraMap, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

end Bridge.CrisIncl.FactorialMulEvaluationLemmas

theorem Bridge.CrisIncl.factorial_mul_ev : ∀ (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (he : PreTilt.untilt e = 1) (h : IsLog l e y) (n : ℕ), ((n.factorial : ℕ) : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)) ⧸ (Reformulated.AutPerF.AinfInv.kerTheta l ↥(PadicComplexInt l)) ^ n) * Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n y = Ideal.Quotient.mk _ (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) * (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) (WittVector.teichmuller l e - 1)) ^ (k + 1)) := by
  intro l _ e y he h n
  obtain ⟨h, rfl⟩ := h
  exact Bridge.CrisIncl.FactorialMulEvaluationLemmas.general _ h n

end
end FactorialMulEvaluation
namespace LogOfPartial
section
structure IsCrisDR (l : ℕ) [Fact l.Prime] (f : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) : Prop where
  on0 : ∀ a : ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)), f (((algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))).comp (algebraMap ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)))) a) = ((algebraMap (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))).comp (algebraMap (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)))) (a : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ∃ (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))),
    f (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) y ∧
      Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n (((l : ℕ) : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ^ N * y) = Ideal.Quotient.mk _ (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a)
def IsLog (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) : Prop :=
  ∃ h, y = Reformulated.AutPerF.BdRPlus.log (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (WittVector.teichmuller l e)) h

namespace Bridge.CrisIncl.LogOfPartialLemmas

open Reformulated.AutPerF

theorem eq_truncLog {B : Type*} [CommRing B] [Algebra ℚ B] (n : ℕ) (c x : B)
    (h : ((n.factorial : ℕ) : B) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : B) * x ^ (k + 1)) :
    c = truncLog n x := by
  have hn : ((n.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have hu : IsUnit ((n.factorial : ℕ) : B) := by
    rw [← map_natCast (algebraMap ℚ B)]
    exact (IsUnit.mk0 _ hn).map _
  refine hu.mul_left_cancel ?_
  rw [h, truncLog, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hd : k + 1 ∣ n.factorial :=
    Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk)
  have e1 : ((-1 : B)) ^ k = algebraMap ℚ B ((-1) ^ k) := by simp
  rw [e1, ← map_natCast (algebraMap ℚ B), ← map_natCast (algebraMap ℚ B), Algebra.smul_def,
    ← mul_assoc, ← map_mul, ← map_mul, Nat.cast_div hd (by positivity)]
  congr 2
  push_cast
  ring

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (Ideal.span {(p : R)}) R]

theorem theta_eq_one (u : Ainf p R) (hu : Ainf.theta p R u = 1) :
    BdRPlus.theta p R (algebraMap (Ainf p R) (BdRPlus p R) u) = 1 := by
  rw [BdRPlus.theta_algebraMap_ainf, hu, map_one]

theorem eq_log (u : Ainf p R) (hu : BdRPlus.theta p R (algebraMap (Ainf p R) (BdRPlus p R) u) = 1)
    (y : BdRPlus p R)
    (h : ∀ n : ℕ, ∃ c : AinfInv p R, ((n.factorial : ℕ) : AinfInv p R) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : AinfInv p R) *
        (algebraMap (Ainf p R) (AinfInv p R) (u - 1)) ^ (k + 1) ∧
      BdRPlus.eval p R n y = Ideal.Quotient.mk _ c) :
    y = BdRPlus.log (algebraMap (Ainf p R) (BdRPlus p R) u) hu := by
  refine BdRPlus.ext_eval fun n => ?_
  obtain ⟨c, hc, hy⟩ := h n
  have e : algebraMap (Ainf p R) (BdRPlus p R) u - 1 =
      algebraMap (AinfInv p R) (BdRPlus p R) (algebraMap (Ainf p R) (AinfInv p R) (u - 1)) := by
    rw [← IsScalarTower.algebraMap_apply, map_sub, map_one]
  rw [hy, BdRPlus.eval_log, eq_truncLog n c _ hc, map_truncLog, e, BdRPlus.eval_algebraMap]

end Bridge.CrisIncl.LogOfPartialLemmas

theorem Bridge.CrisIncl.isLog_of_partial : ∀ (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (he : PreTilt.untilt e = 1) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (h : ∀ n : ℕ, ∃ c : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)), ((n.factorial : ℕ) : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) * c = ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) * (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) (WittVector.teichmuller l e - 1)) ^ (k + 1) ∧ Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n y = Ideal.Quotient.mk _ c), IsLog l e y := by
  intro l _ e he y h
  exact ⟨Bridge.CrisIncl.LogOfPartialLemmas.theta_eq_one _
      ((Reformulated.AutPerF.Ainf.theta_teich e).trans he),
    Bridge.CrisIncl.LogOfPartialLemmas.eq_log _ _ y h⟩

end
end LogOfPartial
namespace CrisDeRhamLogStructure
section
structure IsCrisDR (l : ℕ) [Fact l.Prime] (f : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) : Prop where
  on0 : ∀ a : ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)), f (((algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))).comp (algebraMap ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)))) a) = ((algebraMap (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))).comp (algebraMap (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)))) (a : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ∃ (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))),
    f (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) y ∧
      Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n (((l : ℕ) : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ^ N * y) = Ideal.Quotient.mk _ (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a)
def IsLog (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) : Prop :=
  ∃ h, y = Reformulated.AutPerF.BdRPlus.log (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (WittVector.teichmuller l e)) h

end
end CrisDeRhamLogStructure
