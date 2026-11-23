import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.FactorialMulTruncLog
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

noncomputable section
namespace GlobalTheory.CrisMaps
open Formalism
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

@[irreducible] def frob (l : ℕ) [Fact l.Prime] : Per.Acris l →+* Per.Acris l := Reformulated.AutPerF.Acris.frob l (Per.OC l)

@[irreducible] def gal (g : Per.Gq l) : Per.Acris l →+* Per.Acris l := Reformulated.AutPerF.Acris.map l (Per.σO g)

structure Extends (f : Per.Ainf l →+* Per.Ainf l) (F : Per.Acris l →+* Per.Acris l) : Prop where
  mem : ∀ y ∈ Per.Acris0 l, Per.extP f y ∈ Per.Acris0 l
  env : ∀ s : Per.Acris0 l, F (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
    algebraMap (Per.Acris0 l) (Per.Acris l) ⟨Per.extP f s, mem _ s.2⟩
  alg : ∀ a : Per.Ainf l, F (algebraMap (Per.Ainf l) (Per.Acris l) a) = algebraMap (Per.Ainf l) (Per.Acris l) (f a)

theorem frob_extends (l : ℕ) [Fact l.Prime] : Extends (Per.φA l) (frob l) := by
  unfold frob; first | exact (fun h => ⟨h.mem, h.env, h.alg⟩) (FrobeniusExtendsCris.Bridge.CrisMaps.frob_extends ..)

theorem gal_extends (g : Per.Gq l) : Extends (Per.σA g) (gal g) := by
  unfold gal; first | exact (fun h => ⟨h.mem, h.env, h.alg⟩) (FrobeniusExtendsStructure.Bridge.CrisMaps.gal_extends ..)

theorem frob_gal (g : Per.Gq l) (x : Per.Acris l) : frob l (gal g x) = gal g (frob l x) := by
  unfold frob gal; first | exact @FrobeniusGalois.Bridge.CrisMaps.frob_gal | exact FrobeniusGalois.Bridge.CrisMaps.frob_gal .. | (intros; apply FrobeniusGalois.Bridge.CrisMaps.frob_gal <;> assumption)

theorem φB_algebraMap (l : ℕ) [Fact l.Prime] (x : Per.Acris l) :
    Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (frob l x) := by
  unfold frob; first | exact @FrobeniusPeriodAlgebraMap.Bridge.CrisMaps.φB_algebraMap | exact FrobeniusPeriodAlgebraMap.Bridge.CrisMaps.φB_algebraMap .. | (intros; apply FrobeniusPeriodAlgebraMap.Bridge.CrisMaps.φB_algebraMap <;> assumption)

theorem σB_algebraMap (g : Per.Gq l) (x : Per.Acris l) :
    Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (gal g x) := by
  unfold gal; first | exact @CrisFrobeniusAlgebraMap.Bridge.CrisMaps.σB_algebraMap | exact CrisFrobeniusAlgebraMap.Bridge.CrisMaps.σB_algebraMap .. | (intros; apply CrisFrobeniusAlgebraMap.Bridge.CrisMaps.σB_algebraMap <;> assumption)

end GlobalTheory.CrisMaps
end
