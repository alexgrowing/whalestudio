import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped nonZeroDivisors TensorProduct

open scoped GroundTheory.Global.AdeleBaseChange

namespace GlobalTheory.IdeleTensorParts

open GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_eq_zero_iff (u : AF F) (z : AE F E) :
    u • z = 0 ↔ algebraMap (AF F) (AdeleRing (𝓞 E) E) u * adeleTensorAlgEquivLeft F E z = 0 := by
  rw [← Algebra.smul_def, ← map_smul, map_eq_zero_iff _ (adeleTensorAlgEquivLeft F E).injective]

theorem fst_iff (z : AE F E) :
    (∀ u : AF F, u.1 = 0 → u • z = 0) ↔ (adeleTensorAlgEquivLeft F E z).2 = 0 := by
  simp only [smul_eq_zero_iff]
  constructor
  · intro h
    have h1 := congrArg Prod.snd (h (0, 1) rfl)
    change finiteAdeleMap F E 1 * (adeleTensorAlgEquivLeft F E z).2 = 0 at h1
    rwa [map_one, one_mul] at h1
  · intro h u hu
    refine Prod.ext ?_ ?_
    · change GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) u.1 * (adeleTensorAlgEquivLeft F E z).1 = 0
      rw [hu, map_zero, zero_mul]
    · change finiteAdeleMap F E u.2 * (adeleTensorAlgEquivLeft F E z).2 = 0
      rw [h, mul_zero]

theorem snd_iff (z : AE F E) :
    (∀ u : AF F, u.2 = 0 → u • z = 0) ↔ (adeleTensorAlgEquivLeft F E z).1 = 0 := by
  simp only [smul_eq_zero_iff]
  constructor
  · intro h
    have h1 := congrArg Prod.fst (h (1, 0) rfl)
    change GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) 1 * (adeleTensorAlgEquivLeft F E z).1 = 0 at h1
    rwa [map_one, one_mul] at h1
  · intro h u hu
    refine Prod.ext ?_ ?_
    · change GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) u.1 * (adeleTensorAlgEquivLeft F E z).1 = 0
      rw [h, mul_zero]
    · change finiteAdeleMap F E u.2 * (adeleTensorAlgEquivLeft F E z).2 = 0
      rw [hu, map_zero, zero_mul]

theorem mem_idelesAt_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (l : (AE F E)ˣ),
    (l ∈ idelesAt E (evI F) ↔ ((GlobalTheory.IdeleLogHom.toE F E l : AdeleRing (𝓞 E) E)).2 = 1) ∧
    (l ∈ idelesAt E (fun x : AF F => x.2) ↔ ((GlobalTheory.IdeleLogHom.toE F E l : AdeleRing (𝓞 E) E)).1 = 1) := by
  intro F E _ _ _ _ _ l
  have e : adeleTensorAlgEquivLeft F E ((l : AE F E) - 1) =
      (GlobalTheory.IdeleLogHom.toE F E l : AdeleRing (𝓞 E) E) - 1 := by
    rw [map_sub, map_one]; rfl
  have hI : ∀ u : AF F, evI F u = 0 ↔ u.1 = 0 := fun u =>
    map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  constructor
  · rw [mem_idelesAt, ← sub_eq_zero]
    refine Iff.trans ?_ ((fst_iff ((l : AE F E) - 1)).trans (by rw [e]; rfl))
    simp only [At, hI]
  · rw [mem_idelesAt, ← sub_eq_zero]
    exact (snd_iff ((l : AE F E) - 1)).trans (by rw [e]; rfl)

end GlobalTheory.IdeleTensorParts
