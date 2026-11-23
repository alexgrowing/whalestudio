import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

namespace GlobalTheory

theorem fdint_mem_finiteDimensional : ∀ {D Ω₁ Ω₂ : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (m₁ : Measure Ω₁) (m₂ : Measure Ω₂) [IsFiniteMeasure m₁] [SFinite m₂] (V : Submodule ℂ (SchwartzMap D ℂ)),
    FiniteDimensional ℂ V → ∀ G : Ω₁ → Ω₂ → SchwartzMap D ℂ, (∀ k l, G k l ∈ V) →
    (∀ y, StronglyMeasurable (Function.uncurry fun k l => iteratedFDeriv ℝ 0 (⇑(G k l)) y)) →
    (∃ (C : ℝ) (w : Ω₂ → ℝ), Integrable w m₂ ∧ ∀ k l, SchwartzMap.seminorm ℂ 0 0 (G k l) ≤ C * w l) →
    ∃ g ∈ V, ⇑g = fun y => ∫ k, ∫ l, G k l y ∂m₂ ∂m₁ := by
  intro D Ω₁ Ω₂ _ _ _ _ m₁ m₂ _ _ V hV G hGV hmeas hCw
  obtain ⟨C, w, hw, hbd⟩ := hCw
  let Ψ : ∀ S : Finset D, V →ₗ[ℂ] (S → ℂ) := fun S =>
    LinearMap.pi fun s =>
      { toFun := fun f => (f : SchwartzMap D ℂ) s
        map_add' := fun f g => by simp
        map_smul' := fun c f => by simp }
  obtain ⟨_, ⟨S, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min
    (Set.range fun S => LinearMap.ker (Ψ S)) ⟨_, ⟨∅, rfl⟩⟩
  have hker : LinearMap.ker (Ψ S) = ⊥ := by
    by_contra hne
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hf1 : (f : SchwartzMap D ℂ) ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨y, hy⟩ : ∃ y, (f : SchwartzMap D ℂ) y ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf1 (SchwartzMap.ext h)
    apply hmin _ ⟨insert y S, rfl⟩
    refine lt_of_le_of_ne ?_ ?_
    · intro g hg
      simp only [LinearMap.mem_ker] at hg ⊢
      funext s
      have := congrFun hg ⟨s, Finset.mem_insert_of_mem s.2⟩
      simpa [Ψ] using this
    · intro h
      have h' : LinearMap.ker (Ψ (insert y S)) = LinearMap.ker (Ψ S) := h
      have hf' : f ∈ LinearMap.ker (Ψ (insert y S)) := by rw [h']; exact hf
      simp only [LinearMap.mem_ker] at hf'
      have := congrFun hf' ⟨y, Finset.mem_insert_self y S⟩
      exact hy (by simpa [Ψ] using this)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Ψ S) hker
  let F : Ω₁ → Ω₂ → (S → ℂ) := fun k l s => G k l s
  have hLF : ∀ k l, ((L (F k l) : V) : SchwartzMap D ℂ) = G k l := by
    intro k l
    have := LinearMap.congr_fun hL ⟨G k l, hGV k l⟩
    exact congrArg Subtype.val this
  have hval : ∀ y, StronglyMeasurable (Function.uncurry fun k l => G k l y) := by
    intro y
    have hc : Continuous fun m : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => D) ℂ => m 0 :=
      continuous_eval_const _
    have := hc.comp_stronglyMeasurable (hmeas y)
    convert this using 1
    funext p
    simp [Function.uncurry, iteratedFDeriv_zero_apply]
  have hFm : StronglyMeasurable (Function.uncurry F) := by
    have : Measurable (Function.uncurry F) := by
      apply measurable_pi_lambda
      intro s
      exact (hval s).measurable
    exact this.stronglyMeasurable
  have hnorm : ∀ k l, ‖F k l‖ ≤ C * w l := by
    intro k l
    refine (pi_norm_le_iff_of_nonneg ?_).2 fun s => ?_
    · exact (norm_nonneg _).trans ((SchwartzMap.norm_le_seminorm ℂ (G k l) 0).trans (hbd k l))
    · exact (SchwartzMap.norm_le_seminorm ℂ (G k l) (s : D)).trans (hbd k l)
  have hint_l : ∀ k, Integrable (F k) m₂ := by
    intro k
    refine Integrable.mono' (hw.const_mul C) ?_ (Eventually.of_forall (hnorm k))
    exact (hFm.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  have hint_k : Integrable (fun k => ∫ l, F k l ∂m₂) m₁ := by
    refine Integrable.mono' (integrable_const (∫ l, C * w l ∂m₂))
      (hFm.integral_prod_right).aestronglyMeasurable (Eventually.of_forall fun k => ?_)
    exact norm_integral_le_of_norm_le (hw.const_mul C) (Eventually.of_forall (hnorm k))
  refine ⟨((L (∫ k, ∫ l, F k l ∂m₂ ∂m₁) : V) : SchwartzMap D ℂ), (L _).2, ?_⟩
  funext y
  let ev : (S → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => ((L v : V) : SchwartzMap D ℂ) y
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let evc : (S → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap ev
  have hev : ∀ v, evc v = ((L v : V) : SchwartzMap D ℂ) y := fun v => rfl
  rw [← hev, ← evc.integral_comp_comm hint_k]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only
  rw [← evc.integral_comp_comm (hint_l k)]
  refine integral_congr_ae (Eventually.of_forall fun l => ?_)
  simp only
  rw [hev, hLF]

end GlobalTheory
