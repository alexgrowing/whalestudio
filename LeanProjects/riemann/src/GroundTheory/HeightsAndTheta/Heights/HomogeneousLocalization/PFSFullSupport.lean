import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace SectionsLatticeFS

lemma FSFullSupport.inter_chartDomain_nonempty {N : ℕ} {U : Set (CP N)} (hU : IsOpen U)
    (hne : U.Nonempty) : (U ∩ CP.chartDomain 0).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  induction x using Projectivization.ind with
  | h v hv =>
    rw [ProjTopology.isOpen_iff] at hU
    obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
    let g : ℂ → (Fin (N + 1) → ℂ) := fun t => v + t • Pi.single 0 1
    have hg : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
    have hvO : v ∈ O := by
      have : (⟨v, hv⟩ : {w : Fin (N + 1) → ℂ // w ≠ 0}) ∈ Projectivization.mk' ℂ ⁻¹' U := hx
      rw [← hOU] at this
      exact this
    have h0 : (g ⁻¹' O).Nonempty := ⟨0, by simpa [g] using hvO⟩
    obtain ⟨t, htO, ht⟩ :=
      (dense_compl_singleton (-(v 0))).inter_open_nonempty _ (hO.preimage hg) h0
    have hw0 : g t 0 ≠ 0 := by
      intro h
      apply ht
      simp only [g, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
      simp only [mem_singleton_iff]
      linear_combination h
    have hw : g t ≠ 0 := fun h => hw0 (by rw [h]; rfl)
    refine ⟨Projectivization.mk ℂ (g t) hw, ?_, hw0⟩
    have : (⟨g t, hw⟩ : {w : Fin (N + 1) → ℂ // w ≠ 0}) ∈ Subtype.val ⁻¹' O := htO
    rw [hOU] at this
    exact this

theorem FSFullSupport.proof : FSFullSupport.Statement := by
  intro N U hU hne
  obtain ⟨x, hxU, hx0⟩ := FSFullSupport.inter_chartDomain_nonempty hU hne
  rw [CP.fsMeasure, Measure.map_apply (CP.measurable_chartInv 0) hU.measurableSet, CP.fsChartMeasure,
    pos_iff_ne_zero, Ne,
    withDensity_apply_eq_zero' (CP.measurable_fsVolumeDensity 0).ennreal_ofReal.aemeasurable]
  have hset : {z : Fin N → ℂ | ENNReal.ofReal (CP.fsVolumeDensity 0 z) ≠ 0} = univ := by
    ext z
    simp [CP.fsVolumeDensity_pos 0 z]
  rw [hset, univ_inter, ← Ne, ← pos_iff_ne_zero]
  refine ((CP.continuous_chartInv 0).isOpen_preimage U hU).measure_pos volume
    ⟨CP.chartCoord 0 x, ?_⟩
  simpa [CP.chartInv_chartCoord 0 hx0] using hxU

example : 0 < CP.fsMeasure 1 univ := FSFullSupport.proof 1 univ isOpen_univ univ_nonempty

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
