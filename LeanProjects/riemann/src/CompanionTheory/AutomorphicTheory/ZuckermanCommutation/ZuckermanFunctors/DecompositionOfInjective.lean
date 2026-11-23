import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsFRepDualStandardUnitaryRep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem decomposition_of_injective : DecOfInj := by
  intro O N _ _ Hom C S _ X T hs hj hm hi
  classical
  choose i hi hi0 using hi
  have hp : ∀ s, ∃ p, Hom X (T s) p ∧ p ∘ₗ i s = LinearMap.id ∧ p ≠ 0 := by
    intro s
    obtain ⟨y, hy⟩ : ∃ y, i s y ≠ 0 := by
      by_contra hn
      exact hi0 s (LinearMap.ext fun y => not_not.1 fun h => hn ⟨y, h⟩)
    obtain ⟨t, p, hp, hpy⟩ : ∃ t p, Hom X (T t) p ∧ p (i s y) ≠ 0 := by
      by_contra hn
      exact hy (hj _ fun t p hp => not_not.1 fun h => hn ⟨t, p, hp, h⟩)
    obtain rfl : s = t := by
      by_contra hst
      exact hpy (LinearMap.congr_fun (hs.2.2 s t hst _ (C.comp _ _ _ _ _ (hi s) hp)) y)
    obtain ⟨c, hc⟩ := hs.2.1 s _ (C.comp _ _ _ _ _ (hi s) hp)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hpy (by simpa using LinearMap.congr_fun hc y)
    refine ⟨c⁻¹ • p, C.smul _ _ _ _ hp, ?_, fun h0 => hpy ?_⟩
    · rw [LinearMap.smul_comp, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · rw [(smul_eq_zero.1 h0).resolve_left (inv_ne_zero hc0)]; rfl
  choose p hp hpi hp0 using hp
  have hne : ∀ s t, s ≠ t → p s ∘ₗ i t = 0 := fun s t hst =>
    hs.2.2 t s (Ne.symm hst) _ (C.comp _ _ _ _ _ (hi t) (hp s))
  refine ⟨i, p, hi, hp, LinearMap.ext fun x => ?_, hpi, hne⟩
  rw [LinearMap.id_apply, eq_comm, ← sub_eq_zero]
  refine hj _ fun t q hq => ?_
  have h0 : p t (x - (∑ s, i s ∘ₗ p s) x) = 0 := by
    rw [map_sub, LinearMap.sum_apply, map_sum, Finset.sum_eq_single t]
    · exact sub_eq_zero.2 (LinearMap.congr_fun (hpi t) (p t x)).symm
    · intro s _ hst
      exact LinearMap.congr_fun (hne t s (Ne.symm hst)) (p s x)
    · simp
  obtain ⟨α, β, hab, h1⟩ := hm t q (p t) hq (hp t)
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at h1
    exact hp0 t ((smul_eq_zero.1 h1).resolve_left (hab.resolve_left (not_not.2 rfl)))
  have h2 := LinearMap.congr_fun h1 (x - (∑ s, i s ∘ₗ p s) x)
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, h0, smul_zero, add_zero] at h2
  exact (smul_eq_zero.1 h2).resolve_left hα

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trivial_rep_admissible : OKTriv := fun _ _ =>
  ⟨rfl, fun _ _ _ _ => (Matrix.one_mul _).symm,
    fun _ _ _ _ => ⟨Set.univ, _, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    ⟨1, fun _ _ _ _ => by simp⟩⟩

theorem vector_rep_admissible : OKVr := by
  intro k r b
  cases b
  · refine ⟨rfl, fun _ _ _ _ => rfl, fun c d _ _ => ?_, ⟨1, fun g _ c d => ?_⟩⟩
    · exact ⟨Set.univ, fun g => g c d, isOpen_univ, trivial,
        (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ c d)).contDiff.contDiffOn, fun _ _ _ => rfl⟩
    · simpa using GlobalTheory.DualFRep.entry_le g c d
  · obtain ⟨-, -, h1, h2, -, -, h3, -⟩ := GlobalTheory.isFRep_dualM k r
    refine ⟨h1, h2, fun c d _ _ => ?_, h3⟩
    let A : Mx k r →ₗ[ℝ] ℂ :=
      { toFun := fun x => (PI.UpqRep.Hpk k r * xᴴ * PI.UpqRep.Hpk k r) d c
        map_add' := fun a b => by rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]; rfl
        map_smul' := fun t a => by
          rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, star_trivial]; rfl }
    refine ⟨Set.univ, A, isOpen_univ, trivial, (LinearMap.toContinuousLinearMap A).contDiff.contDiffOn,
      fun g _ hg => ?_⟩
    show g⁻¹ d c = _
    rw [PI.HwUniqW.inv_eq_UH hg]; rfl

end CompanionTheory.Zuck

end
