import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
import GroundTheory.GlobalFields.NormResidueSymbol.Infinite
import GroundTheory.GlobalFields.NormResidueSymbol.AbstractUnique
import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

abbrev galCommGroup : CommGroup (L ≃ₐ[K] L) :=
  { toGroup := (inferInstance : Group (L ≃ₐ[K] L)), mul_comm := mul_comm' }

attribute [local instance] galCommGroup

def ideleSymbol : IdeleGroup K →* (L ≃ₐ[K] L) :=
  IdeleMap.ideleMap (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L)

variable {K}

theorem ideleSymbol_apply (x : IdeleGroup K) :
    ideleSymbol K L x = (∏ᶠ v, localSymbol L v (finiteProj v x)) *
      ∏ w, infiniteLocalSymbol L w (infiniteProj w x) :=
  IdeleMap.ideleMap_apply (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) x

theorem hasFiniteMulSupport_localSymbol (x : IdeleGroup K) :
    Function.HasFiniteMulSupport fun v ↦ localSymbol L v (finiteProj v x) :=
  IdeleMap.hasFiniteMulSupport (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v)
    (eventually_units_le_ker_localSymbol L) x

@[simp]
theorem ideleSymbol_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ideleSymbol K L (finiteEmbedding v a) = localSymbol L v a :=
  IdeleMap.ideleMap_finiteEmbedding (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) v a

@[simp]
theorem ideleSymbol_infiniteEmbedding (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleSymbol K L (infiniteEmbedding w a) = infiniteLocalSymbol L w a :=
  IdeleMap.ideleMap_infiniteEmbedding (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) w a

theorem continuous_ideleSymbol : Continuous (ideleSymbol K L) :=
  IdeleMap.continuous_ideleMap (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) (fun v ↦ continuous_localSymbol L v)
    (fun w ↦ continuous_infiniteLocalSymbol L w)

theorem isOpen_ker_ideleSymbol : IsOpen ((ideleSymbol K L).ker : Set (IdeleGroup K)) := by
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete _).preimage (continuous_ideleSymbol L)

theorem eq_ideleSymbol {ψ : IdeleGroup K →* (L ≃ₐ[K] L)} (hψ : Continuous ψ)
    (hfin : ∀ v a, ψ (finiteEmbedding v a) = localSymbol L v a)
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = infiniteLocalSymbol L w a) :
    ψ = ideleSymbol K L :=
  IdeleMap.eq_ideleMap (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) (fun v ↦ continuous_localSymbol L v)
    (fun w ↦ continuous_infiniteLocalSymbol L w) hψ
    (fun v ↦ MonoidHom.ext (hfin v)) (fun w ↦ MonoidHom.ext (hinf w))

theorem range_ideleNorm_le_ker_ideleSymbol : (ideleNorm K L).range ≤ (ideleSymbol K L).ker := by
  intro x hx
  obtain ⟨hf, hi⟩ := (IdeleNorm.mem_range_ideleNorm_iff_forall L x).1 hx
  exact IdeleMap.ideleMap_eq_one_of_forall_mem (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L)
    (fun v ↦ (IdeleNorm.finiteLocalNorm L v).range)
    (fun w ↦ (IdeleNorm.infiniteLocalNorm L w).range)
    (fun v ↦ range_finiteLocalNorm_le_ker_localSymbol L v)
    (fun w ↦ range_infiniteLocalNorm_le_ker_infiniteLocalSymbol L w) hf hi

@[simp]
theorem ideleSymbol_ideleNorm (y : IdeleGroup L) : ideleSymbol K L (ideleNorm K L y) = 1 :=
  range_ideleNorm_le_ker_ideleSymbol L ⟨y, rfl⟩

end

end GroundTheory.Global
