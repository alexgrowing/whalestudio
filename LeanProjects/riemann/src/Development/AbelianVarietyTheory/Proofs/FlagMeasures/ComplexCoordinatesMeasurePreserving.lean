import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.ReImVolume

noncomputable def reImLinear (ι : Type) (n : ℕ) :
    (ι → Fin n → ℂ) ≃ₗ[ℝ] (ι × Fin n × Bool → ℝ) where
  toFun y p := if p.2.2 then (y p.1 p.2.1).re else (y p.1 p.2.1).im
  invFun x v i := ⟨x (v, i, true), x (v, i, false)⟩
  map_add' y z := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  map_smul' c y := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  left_inv y := by
    funext v i
    simp
  right_inv x := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp

theorem volume_re_im (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume {z : ℂ | z.re ∈ A ∧ z.im ∈ B} = volume A * volume B := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (hA.prod hB).nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_prod] at h
  rw [← h]
  rfl

theorem measurePreserving_reImLinear (ι : Type) [Fintype ι] (n : ℕ) :
    MeasurePreserving (reImLinear ι n) volume volume := by
  have hm : Measurable (reImLinear ι n) :=
    (reImLinear ι n).toLinearMap.continuous_of_finiteDimensional.measurable
  refine ⟨hm, ?_⟩
  rw [volume_pi (α := fun _ : ι × Fin n × Bool => ℝ)]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (reImLinear ι n) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun v => Set.univ.pi fun i =>
        {z : ℂ | z.re ∈ s (v, i, true) ∧ z.im ∈ s (v, i, false)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_setOf_eq]
    constructor
    · intro h v i
      exact ⟨h (v, i, true), h (v, i, false)⟩
    · rintro h ⟨v, i, _ | _⟩
      · exact (h v i).2
      · exact (h v i).1
  rw [hpre, volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool, volume_re_im _ _ (hs _) (hs _)]

theorem exists_reIm_measurePreserving :
    ∀ (ι : Type) [Fintype ι] (n : ℕ), ∃ T : (ι → Fin n → ℂ) ≃ₜ+ (ι × Fin n × Bool → ℝ),
      MeasurePreserving T volume volume ∧
        ∀ y v i, T y (v, i, true) = (y v i).re ∧ T y (v, i, false) = (y v i).im := by
  intro ι _ n
  let L := (reImLinear ι n).toContinuousLinearEquiv
  refine ⟨{ toAddEquiv := (reImLinear ι n).toAddEquiv
            continuous_toFun := L.continuous
            continuous_invFun := L.symm.continuous }, ?_, fun y v i => ⟨rfl, rfl⟩⟩
  exact measurePreserving_reImLinear ι n

end GlobalTheory.ReImVolume
