import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped nonZeroDivisors TensorProduct

noncomputable section

namespace GlobalTheory.LocIdealAdele

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem snd_apply (z : AE F E) (w : HeightOneSpectrum (𝓞 E)) :
    (adeleTensorAlgEquivLeft F E z).2 w =
      SemiLocal.tensorMap E (below F w) (compFin F E (below F w) z) ⟨w, liesOver_below w⟩ := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul a x =>
    have h : compFin F E (below F w) (a ⊗ₜ[F] x) = (a.2 (below F w)) ⊗ₜ[F] x := rfl
    rw [h, SemiLocal.tensorMap_tmul, mul_comm]
    exact congrArg (fun y : AdeleRing (𝓞 E) E => y.2 w) (adeleTensorAlgEquivLeft_tmul a x)
  | add a b ha hb =>
    rw [map_add, map_add, map_add, Pi.add_apply, ← ha, ← hb]
    rfl

theorem valued_le {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) (w : HeightOneSpectrum (𝓞 E))
    {y : Fv F (below F w) ⊗[F] E} (hy : y ∈ GlobalTheory.LocIdeal.locId (below F w) 𝔞) :
    Valued.v (SemiLocal.tensorMap E (below F w) y ⟨w, liesOver_below w⟩) ≤
      WithZero.exp (-FractionalIdeal.count E w 𝔞) := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    rw [SemiLocal.tensorMap_tmul]
    haveI := liesOver_below (K := F) w
    change Valued.v (SemiLocal.completionMap (below F w) w a * algebraMap E (w.adicCompletion E) x) ≤ _
    rw [map_mul, SemiLocal.valued_completionMap]
    have h1 : Valued.v a ≤ 1 := ha
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) x) ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞) := by
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        Algebra.algebraMap_self, RingHom.id_apply]
      exact (GlobalTheory.Idele.mem_iff_valuation_le h𝔞 x).1 hx w
    exact (mul_le_mul' (pow_le_one' h1 _) h2).trans_eq (one_mul _)
  | zero => rw [map_zero, Pi.zero_apply, map_zero]; exact zero_le
  | add a b _ _ ha hb =>
    rw [map_add, Pi.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  | neg a _ ha =>
    rw [map_neg, Pi.neg_apply, Valuation.map_neg]
    exact ha

theorem mem_idealFiniteAdeles_of_locId : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (z : AE F E),
    (∀ v : Pl F, compFin F E v z ∈ GlobalTheory.LocIdeal.locId v 𝔞) →
    (GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft F E z).2 ∈ GroundTheory.Global.idealFiniteAdeles (Units.mk0 𝔞 h𝔞) := by
  intro F E _ _ _ _ _ 𝔞 h𝔞 z hz w
  rw [snd_apply]
  exact valued_le h𝔞 w (hz _)

end GlobalTheory.LocIdealAdele

end
