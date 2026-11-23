import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups

namespace GroundTheory.Global

open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal

noncomputable section

namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

attribute [local instance] FractionRing.liftAlgebra in
variable (K L) in

theorem eventually_ramificationIdx_eq_one :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  rw [eventually_cofinite]
  refine (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset
    fun w hw ↦ ?_
  by_contra h
  have := w.isPrime
  have := not_dvd_differentIdeal_iff.1 h
  exact hw (Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 K))

theorem map_integerUnitsOver_eq_of_ramificationIdx_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : PlacesOver L v) (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (integerUnitsOver L v).map (finiteLocalNorm L v) =
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  classical
  refine le_antisymm (map_integerUnitsOver_le v) fun u hu ↦ ?_
  obtain ⟨y, hy, hyu⟩ := exists_norm_eq_of_ramificationIdx_eq_one v w.1 he hu
  refine ⟨Pi.mulSingle w y, mem_integerUnitsOver.2 fun w' ↦ ?_, ?_⟩
  · by_cases h : w' = w
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact hy
    · rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  · rw [finiteLocalNorm_mulSingle]
    exact Units.ext hyu

variable (L) in

theorem eventually_map_integerUnitsOver_eq :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      (integerUnitsOver L v).map (finiteLocalNorm L v) =
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  refine (eventually_forall_placesOver K (eventually_ramificationIdx_eq_one K L)).mono
    fun v hv ↦ ?_
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w (hv w)

variable (L) in

theorem mem_range_ideleNorm_iff_forall (x : IdeleGroup K) :
    x ∈ (ideleNorm K L).range ↔
      (∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range) ∧
      ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range := by
  rw [mem_range_ideleNorm_iff]
  refine ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, ?_⟩⟩
  filter_upwards [eventually_finiteProj_mem (L := K) x, eventually_map_integerUnitsOver_eq L]
    with v hv hv'
  rw [hv']
  exact hv

theorem mem_range_ideleNorm_of_forall (x : IdeleGroup K)
    (hfin : ∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range)
    (hinf : ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range) :
    x ∈ (ideleNorm K L).range :=
  (mem_range_ideleNorm_iff_forall L x).2 ⟨hfin, hinf⟩

end IdeleNorm

end

end GroundTheory.Global
