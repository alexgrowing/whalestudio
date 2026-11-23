import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SecondCountableQuotients.QuotientMeasureUnitaryGroup

open MeasureTheory MeasureTheory.Measure Matrix

noncomputable section

namespace CompanionTheory.D.Upq.Quot

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula CompanionTheory.D.Upq.ModEx

variable {m : ℕ}

theorem exists_isHaarOnM {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) :
    ∃ μ : Measure (MtM m), IsHaarOnM G μ := by
  have hι := MG.measurableEmbedding_toM (hG := hG)
  let μ : Measure (MG G hG) := haar
  refine ⟨μ.map MG.toM, hι.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · rw [Ne, Measure.map_eq_zero_iff hι.measurable.aemeasurable]
    exact NeZero.ne μ
  · rw [hι.map_apply]
    have : (MG.toM : MG G hG → MtM m) ⁻¹' {x | Matrix.of x ∉ G} = ∅ :=
      Set.eq_empty_of_forall_notMem fun a ha => ha a.mem
    rw [this, measure_empty]
  · have e : lmulQ s ∘ MG.toM = MG.toM ∘ (fun x : MG G hG => MG.mk hG s hs * x) := rfl
    rw [map_map (measurable_lmulQ _) hι.measurable, e,
      ← map_map hι.measurable (measurable_const_mul _), map_mul_left_eq_self]

def oneM (m : ℕ) : MtM m := Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ)

theorem quotient_measure_self {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G)
    {μ : Measure (MtM m)} (hμ : IsHaarOnM G μ) (hr : IsRightInvM G μ) :
    QuotientSetting G G μ μ (dirac (oneM m)) := by
  refine ⟨hG, hG, subset_rfl, hμ, hμ, hr, hr, fun f _ => ?_⟩
  rw [lintegral_dirac]
  congr 1
  ext s
  congr 1
  exact (Matrix.mul_one (Matrix.of s)).symm

theorem isMatGroup_one : IsMatGroup ({1} : Set (Matrix (Fin m) (Fin m) ℂ)) :=
  ⟨isClosed_singleton, rfl, fun a ha b hb => by
    rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]; simp, fun a ha => by
    rw [Set.mem_singleton_iff.1 ha]; simp⟩

theorem quotient_measure_trivial_subgroup {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G)
    {μ : Measure (MtM m)} (hμ : IsHaarOnM G μ) (hr : IsRightInvM G μ) :
    QuotientSetting G {1} μ (dirac (oneM m)) μ := by
  refine ⟨hG, isMatGroup_one, Set.singleton_subset_iff.2 hG.2.1, hμ,
    ⟨inferInstance, NeZero.ne _, ?_, fun s hs => ?_⟩, hr, fun s hs => ?_, fun f _ => ?_⟩
  · rw [dirac_apply]
    refine Set.indicator_of_notMem ?_ _
    intro h
    exact h rfl
  · rw [Set.mem_singleton_iff.1 hs, map_dirac' (measurable_lmulQ _)]
    congr 1
    exact Matrix.mul_one (1 : Matrix (Fin m) (Fin m) ℂ)
  · rw [Set.mem_singleton_iff.1 hs, map_dirac' (measurable_rmulQ _)]
    congr 1
    exact Matrix.mul_one (1 : Matrix (Fin m) (Fin m) ℂ)
  · congr 1
    ext x
    rw [lintegral_dirac]
    congr 1
    exact (Matrix.one_mul (Matrix.of x)).symm

theorem exists_quotient_measure_unitary_group (k r : ℕ) : ∃ μ : Measure (MtM (2 * r + k + 1)),
    QuotientSetting (UH (Hpk k r)) (UH (Hpk k r)) μ μ (dirac (oneM _)) ∧
    QuotientSetting (UH (Hpk k r)) {1} μ (dirac (oneM _)) μ := by
  have hG := unitary_hermitian_group k r
  obtain ⟨μ, hμ⟩ := exists_isHaarOnM hG
  obtain ⟨D, hD, hR⟩ := exists_modular_function _ _ hG
  have hr := hR (CompanionTheory.D.Upq.unitary_group_modular_function_trivial k r D hD) μ hμ
  exact ⟨μ, quotient_measure_self hG hμ hr, quotient_measure_trivial_subgroup hG hμ hr⟩

end CompanionTheory.D.Upq.Quot

end
