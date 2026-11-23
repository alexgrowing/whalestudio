import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.PadicField
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
namespace LogSeriesAlt
section
structure IsCrisDR (l : ℕ) [Fact l.Prime] (f : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) : Prop where
  on0 : ∀ a : ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)), f (((algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))).comp (algebraMap ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)))) a) = ((algebraMap (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))).comp (algebraMap (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)))) (a : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ∃ (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))),
    f (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) y ∧
      Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n (((l : ℕ) : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ^ N * y) = Ideal.Quotient.mk _ (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a)
def IsLog (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) : Prop :=
  ∃ h, y = Reformulated.AutPerF.BdRPlus.log (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (WittVector.teichmuller l e)) h

namespace Bridge.CrisIncl.LogSeriesLemmas

open Reformulated.AutPerF

variable {p : ℕ} [Fact p.Prime]
variable {R : Type*} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R]

end Bridge.CrisIncl.LogSeriesLemmas

end
end LogSeriesAlt
namespace CrisRestriction
section
structure IsCrisDR (l : ℕ) [Fact l.Prime] (f : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) : Prop where
  on0 : ∀ a : ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)), f (((algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))).comp (algebraMap ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)))) a) = ((algebraMap (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))).comp (algebraMap (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)))) (a : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ∃ (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))),
    f (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) y ∧
      Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n (((l : ℕ) : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ^ N * y) = Ideal.Quotient.mk _ (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a)
def IsLog (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) : Prop :=
  ∃ h, y = Reformulated.AutPerF.BdRPlus.log (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (WittVector.teichmuller l e)) h

namespace Bridge.CrisIncl.CrisRestrictionLemmas

theorem exists_factor {A B C : Type*} [Ring A] [Ring B] [Ring C] (f : A →+* C) (g : B →+* C)
    (hg : Function.Injective g) (h : ∀ x, ∃ y, f x = g y) :
    ∃ j : A →+* B, ∀ x, f x = g (j x) := by
  choose j hj using h
  refine ⟨⟨⟨⟨j, ?_⟩, ?_⟩, ?_, ?_⟩, hj⟩
  · apply hg
    rw [← hj, map_one, map_one]
  · intro x y
    apply hg
    simp only [map_mul, ← hj]
  · apply hg
    simp only [map_zero, ← hj]
  · intro x y
    apply hg
    simp only [map_add, ← hj]

end Bridge.CrisIncl.CrisRestrictionLemmas

theorem Bridge.CrisIncl.exists_restrict : ∀ (l : ℕ) [Fact l.Prime] (ι : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) (h : IsCrisDR l ι), ∃ j : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)), (∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ι (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) (j x)) ∧ (∀ s : ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)), j (algebraMap (↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) s) = algebraMap ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (s : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)))) ∧ ∀ n : ℕ, ∃ N : ℕ, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ∃ a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l)), Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n (((l : ℕ) : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ^ N * j x) = Ideal.Quotient.mk _ (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a) := by
  intro l _ ι h
  have hg : Function.Injective (algebraMap (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))
      (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) := IsFractionRing.injective _ _
  obtain ⟨j, hj⟩ := Bridge.CrisIncl.CrisRestrictionLemmas.exists_factor
    (ι.comp (algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))
      (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)))) _ hg (fun x => by
      obtain ⟨N, hN⟩ := h.bdd 0
      obtain ⟨y, a, hy, -⟩ := hN x
      exact ⟨y, hy⟩)
  refine ⟨j, hj, fun s => hg ((hj _).symm.trans (h.on0 s)), fun n => ?_⟩
  obtain ⟨N, hN⟩ := h.bdd n
  refine ⟨N, fun x => ?_⟩
  obtain ⟨y, a, hy, ha⟩ := hN x
  have e : j x = y := hg ((hj x).symm.trans hy)
  exact ⟨a, e ▸ ha⟩

end
end CrisRestriction
namespace CrisDeRhamLog
section
structure IsCrisDR (l : ℕ) [Fact l.Prime] (f : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) : Prop where
  on0 : ∀ a : ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)), f (((algebraMap (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))).comp (algebraMap ↥(Reformulated.AutPerF.acrisZero l ↥(PadicComplexInt l)) (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)))) a) = ((algebraMap (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))).comp (algebraMap (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)) (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)))) (a : (Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l)))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), ∃ (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (a : (Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))),
    f (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x) = algebraMap ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdR l ↥(PadicComplexInt l))) y ∧
      Reformulated.AutPerF.BdRPlus.eval l ↥(PadicComplexInt l) n (((l : ℕ) : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) ^ N * y) = Ideal.Quotient.mk _ (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.AinfInv l ↥(PadicComplexInt l))) a)
def IsLog (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (y : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) : Prop :=
  ∃ h, y = Reformulated.AutPerF.BdRPlus.log (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (WittVector.teichmuller l e)) h

theorem Bridge.CrisIncl.exists_incl : ∀ (l : ℕ) [Fact l.Prime], ∃ ι : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l)), IsCrisDR l ι := by
  intro l _
  refine ⟨Reformulated.AutPerF.Bcris.toBdR l (PadicComplexInt l), fun a => ?_, fun n => ⟨n, fun x => ?_⟩⟩
  · rw [RingHom.comp_apply, RingHom.comp_apply, Reformulated.AutPerF.Bcris.toBdR_algebraMap_acris,
      Reformulated.AutPerF.Acris.toBdRPlus_algebraMap_zero]
  · obtain ⟨b, hb⟩ := Reformulated.AutPerF.AcrisZero.exists_p_pow_mul_eq n
      (Reformulated.AutPerF.Acris.toRange l (PadicComplexInt l) n x)
    refine ⟨Reformulated.AutPerF.Acris.toBdRPlus l (PadicComplexInt l) x, b,
      Reformulated.AutPerF.Bcris.toBdR_algebraMap_acris x, ?_⟩
    rw [map_mul, map_pow, map_natCast, Reformulated.AutPerF.Acris.eval_toBdRPlus]
    have h := congrArg Subtype.val hb
    push_cast at h
    exact h

end
end CrisDeRhamLog
