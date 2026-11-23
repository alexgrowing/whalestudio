import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.FactorialMulTruncLog
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison

namespace GlobalTheory.CrisIncl
open Formalism
open scoped Formalism.Per

open Reformulated.AutPerF in

theorem exists_incl (l : ℕ) [Fact l.Prime] : ∃ ι : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l ι := by
  exact (CrisDeRhamLog.Bridge.CrisIncl.exists_incl l).imp fun _ h => ⟨h.1, h.2⟩

theorem exists_restrict (l : ℕ) [Fact l.Prime] (ι : Per.Bcris l →+* Per.BdR l) (h : Per.IsCrisDR l ι) :
    ∃ j : Per.Acris l →+* Per.BdRp l,
      (∀ x : Per.Acris l,
        ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧
      (∀ s : Per.Acris0 l, j (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
        algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) ∧
      ∀ n : ℕ, ∃ N : ℕ, ∀ x : Per.Acris l, ∃ a : Per.Ainf l,
        Per.ev l n (((l : ℕ) : Per.BdRp l) ^ N * j x) =
          Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  exact CrisRestriction.Bridge.CrisIncl.exists_restrict l ι ⟨h.1, h.2⟩

theorem factorial_mul_ev (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (y : Per.BdRp l) (he : e.untilt = 1)
    (h : Per.IsLog l e y) (n : ℕ) :
    ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * Per.ev l n y =
      Ideal.Quotient.mk _ (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1)) ^ (k + 1)) := by
  first | exact @FactorialMulEvaluation.Bridge.CrisIncl.factorial_mul_ev | exact FactorialMulEvaluation.Bridge.CrisIncl.factorial_mul_ev .. | (intros; apply FactorialMulEvaluation.Bridge.CrisIncl.factorial_mul_ev <;> assumption)

theorem isLog_of_partial (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) (y : Per.BdRp l)
    (h : ∀ n : ℕ, ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1)) ^ (k + 1) ∧
      Per.ev l n y = Ideal.Quotient.mk _ c) : Per.IsLog l e y := by
  first | exact @LogOfPartial.Bridge.CrisIncl.isLog_of_partial | exact LogOfPartial.Bridge.CrisIncl.isLog_of_partial .. | (intros; apply LogOfPartial.Bridge.CrisIncl.isLog_of_partial <;> assumption)

theorem log_unique (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) (y y' : Per.BdRp l)
    (h : Per.IsLog l e y) (h' : Per.IsLog l e y') : y = y' := by
  first | exact @LogUniqueAlt.Bridge.CrisIncl.log_unique | exact LogUniqueAlt.Bridge.CrisIncl.log_unique .. | (intros; apply LogUniqueAlt.Bridge.CrisIncl.log_unique <;> assumption)

theorem incl_aB (l : ℕ) [Fact l.Prime] (ι : Per.Bcris l →+* Per.BdR l) (h : Per.IsCrisDR l ι) (a : Per.Ainf l) :
    ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l)
      (algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) a)) := by
  exact CrisInclusionPeriod.Bridge.CrisIncl.incl_aB l ι ⟨h.1, h.2⟩ a

end GlobalTheory.CrisIncl
