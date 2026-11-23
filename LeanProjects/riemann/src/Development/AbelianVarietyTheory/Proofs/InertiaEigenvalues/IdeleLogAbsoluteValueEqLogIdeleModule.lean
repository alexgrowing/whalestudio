import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.IdeleLogNormCompare

open GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.Mem.Chr.CharModel

variable (E : Type) [Field E] [NumberField E]

theorem ord_eq_ord_vw (d : (AdeleRing (𝓞 E) E)ˣ) (v : HeightOneSpectrum (𝓞 E)) :
    GroundTheory.Global.IdeleGroup.ord v d = GlobalTheory.Idele.ord_vw (finPart E d) v := rfl

theorem logInf_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logInf E (infPart E d) = Real.log (infiniteModule d) := by
  rw [infiniteModule, Real.log_prod]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
    rfl
  · intro w _
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (infinite_ne_zero d w))

theorem logFin_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logFin E (finPart E d) = -Real.log (finiteModule d) := by
  classical
  have hfin := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (finPart E d))
  let S := hfin.toFinset
  have hS : ∀ v, v ∉ S → GlobalTheory.Idele.ord_vw (finPart E d) v = 0 := by
    intro v hv
    by_contra h
    exact hv (hfin.mem_toFinset.2 h)
  have hI : GlobalTheory.Idele.idealOf (finPart E d) =
      ∏ v ∈ S, (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v := by
    unfold GlobalTheory.Idele.idealOf
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    exact hv (by show (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v = 1
                 rw [hS v h, zpow_zero])
  have hM : finiteModule d = ∏ v ∈ S, ‖(d : AdeleRing (𝓞 E) E).2 v‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    refine hv ?_
    change ‖(d : AdeleRing (𝓞 E) E).2 v‖ = 1
    rw [norm_finite_eq_rpow, ord_eq_ord_vw, hS v h, Int.cast_zero, neg_zero, Real.rpow_zero]
  have hN : ∀ v : HeightOneSpectrum (𝓞 E), (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    fun v => (absNorm_asIdeal_pos v).ne'
  rw [logFin, hI, hM, map_prod, Rat.cast_prod, Real.log_prod, Real.log_prod, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow,
      norm_finite_eq_rpow, Real.log_rpow (absNorm_asIdeal_pos v), ord_eq_ord_vw]
    ring
  · intro v _
    exact norm_ne_zero_iff.2 (finite_ne_zero d v)
  · intro v _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    exact zpow_ne_zero _ (hN v)

theorem logNorm_eq_log_ideleModule (d : (AdeleRing (𝓞 E) E)ˣ) :
    logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  rw [logNorm, logInf_eq, logFin_eq, ideleModule_apply,
    Real.log_mul (infiniteModule_pos d).ne' (finiteModule_pos d).ne']
  ring

end GlobalTheory.IdeleLogNormCompare
