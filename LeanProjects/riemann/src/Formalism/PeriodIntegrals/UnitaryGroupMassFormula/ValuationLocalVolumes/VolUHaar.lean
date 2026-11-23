import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdSd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTUnit

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUH

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal TensorProduct

theorem haar_pre {G : Type*} [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsAddHaarMeasure] (φ : G ≃ₜ+ G) (K : Set G) (hK : μ K = 1) (S : Set G) :
    μ (φ ⁻¹' S) = μ (φ ⁻¹' K) * μ S := by
  have he : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  haveI : (μ.map φ).IsAddHaarMeasure :=
    μ.isAddHaarMeasure_map (φ : G →+ G) φ.continuous φ.surjective
      φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have h := Measure.isAddLeftInvariant_eq_smul (μ.map φ) μ
  have key : ∀ T : Set G, μ (φ ⁻¹' T) = (μ.map φ).addHaarScalarFactor μ * μ T := by
    intro T
    rw [← he.map_apply]
    conv_lhs => rw [h]
    simp
  rw [key S, key K, hK, mul_one]

section R

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem top_facts (ι : Type) [Fintype ι] :
    IsTopologicalAddGroup (ι → Fv F v ⊗[F] E) ∧ LocallyCompactSpace (ι → Fv F v ⊗[F] E) ∧
      SecondCountableTopology (ι → Fv F v ⊗[F] E) ∧ BorelSpace (ι → Fv F v ⊗[F] E) ∧
      IsModuleTopology (Fv F v) (ι → Fv F v ⊗[F] E) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

def scMul {ι : Type} [Fintype ι] (z : ι → Fv F v) (hz : ∀ i, z i ≠ 0) :
    (ι → Fv F v ⊗[F] E) ≃ₜ+ (ι → Fv F v ⊗[F] E) where
  toFun w i := sc (E := E) v (z i) * w i
  invFun w i := sc (E := E) v (z i)⁻¹ * w i
  left_inv w := by
    funext i
    simp only
    rw [← mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ (hz i), VolTU.sc_one, one_mul]
  right_inv w := by
    funext i
    simp only
    rw [← mul_assoc, ← VolTU.sc_mul, mul_inv_cancel₀ (hz i), VolTU.sc_one, one_mul]
  map_add' w w' := by
    funext i
    simp only [Pi.add_apply, mul_add]
  continuous_toFun := by
    obtain ⟨-, -, -, -, h⟩ := top_facts (E := E) v ι
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap
      (PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v fun i => sc (E := E) v (z i))
  continuous_invFun := by
    obtain ⟨-, -, -, -, h⟩ := top_facts (E := E) v ι
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap
      (PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v fun i => sc (E := E) v (z i)⁻¹)

theorem sc_pre (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (hK : μ (VolTO (E := E) v ι) = 1) (z : ι → Fv F v) (hz : ∀ i, z i ≠ 0) (S : Set (ι → Fv F v ⊗[F] E)) :
    μ {w | (fun i => sc (E := E) v (z i) * w i) ∈ S} =
      μ {w | ∀ i, sc (E := E) v (z i) * w i ∈ OEv (E := E) v} * μ S := by
  exact haar_pre μ (scMul (E := E) v z hz) _ hK S

theorem sub_pre (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (b : ι → Fv F v ⊗[F] E) (S : Set (ι → Fv F v ⊗[F] E)) :
    μ {w | (fun i => w i - b i) ∈ S} = μ S := by
  have h : {w | (fun i => w i - b i) ∈ S} = (fun w => w + -b) ⁻¹' S := by
    ext w
    simp [sub_eq_add_neg]
    rfl
  rw [h, measure_preimage_add_right]

end R

end Formalism.L2.SG.Pf.NcVal.VolUH
