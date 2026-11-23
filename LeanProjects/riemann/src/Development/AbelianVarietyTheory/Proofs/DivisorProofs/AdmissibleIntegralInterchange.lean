import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousOfSeminormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralOfIntegrableBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralEqOfBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakContinuityDerivativeContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TemperedFunctionalSeminormBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.AdmInt

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

noncomputable def evalAt (x : D) : SchwartzMap D ℂ →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ D ℂ)

theorem exists_iterated_integral_comm {S₁ S₂ : Type} [TopologicalSpace S₁] [SecondCountableTopology S₁]
    [MeasurableSpace S₁] [BorelSpace S₁] [TopologicalSpace S₂] [SecondCountableTopology S₂] [MeasurableSpace S₂]
    [BorelSpace S₂] (μ₁ : Measure S₁) (μ₂ : Measure S₂) [IsFiniteMeasure μ₁] (f : S₁ → S₂ → SchwartzMap D ℂ)
    (hw : ∀ T : SchwartzMap D ℂ →L[ℂ] ℂ, Continuous fun p : S₁ × S₂ => T (f p.1 p.2))
    (hb : ∀ m n : ℕ, ∃ c : S₂ → ℝ, Continuous c ∧ Integrable c μ₂ ∧ ∀ s t, SchwartzMap.seminorm ℂ m n (f s t) ≤ c t) :
    ∃ F : SchwartzMap D ℂ, ∀ T : SchwartzMap D ℂ →L[ℂ] ℂ, (∀ s, Integrable (fun t => T (f s t)) μ₂) ∧
      Integrable (fun s => ∫ t, T (f s t) ∂μ₂) μ₁ ∧ T F = ∫ s, ∫ t, T (f s t) ∂μ₂ ∂μ₁ := by
  choose c hcc hci hcb using hb
  have hwt : ∀ s (T : SchwartzMap D ℂ →L[ℂ] ℂ), Continuous fun t => T (f s t) := fun s T =>
    (hw T).comp (continuous_const.prodMk continuous_id)
  have hG : ∀ s, ∃ G : SchwartzMap D ℂ,
      (∀ (n : ℕ) (x : D), iteratedFDeriv ℝ n G x = ∫ t, iteratedFDeriv ℝ n (f s t) x ∂μ₂) ∧
      ∀ m n, SchwartzMap.seminorm ℂ m n G ≤ ∫ t, c m n t ∂μ₂ := by
    intro s
    have hd := GlobalTheory.T.weak_continuity_derivative_continuous (f s) (hwt s)
    obtain ⟨G, -, hG1, hG2⟩ := GlobalTheory.T.schwartz_integral_of_integrable_bounds μ₂ (f s) (fun n x => (hd n x).aestronglyMeasurable)
      (fun m n => ⟨c m n, hci m n, hcb m n s⟩)
    exact ⟨G, hG1, fun m n => hG2 m n (c m n) (hci m n) (hcb m n s)⟩
  choose G hG1 hG2 using hG
  have hfc : ∀ s, Continuous (f s) := fun s =>
    GlobalTheory.T.schwartz_continuous_of_seminorm_bounds (f s) (GlobalTheory.T.weak_continuity_derivative_continuous (f s) (hwt s)) (fun m n => ⟨c m n, hcc m n, hcb m n s⟩)
  have hTG : ∀ s (T : SchwartzMap D ℂ →L[ℂ] ℂ), T (G s) = ∫ t, T (f s t) ∂μ₂ := fun s T =>
    GlobalTheory.T.schwartz_integral_eq_of_bounds μ₂ (f s) (G s) (hfc s) (fun m n => ⟨c m n, hci m n, hcb m n s⟩) (hG1 s) T
  have hTb : ∀ T : SchwartzMap D ℂ →L[ℂ] ℂ, ∃ b : S₂ → ℝ, Integrable b μ₂ ∧ ∀ s t, ‖T (f s t)‖ ≤ b t := by
    intro T
    obtain ⟨N, C, hC, hT⟩ := GlobalTheory.T.tempered_functional_seminorm_bound T
    refine ⟨fun t => C * ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1), c m n t, ?_, fun s t => ?_⟩
    · exact (integrable_finset_sum _ fun m _ => integrable_finset_sum _ fun n _ => hci m n).const_mul C
    · refine (hT _).trans (mul_le_mul_of_nonneg_left ?_ hC)
      exact Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => hcb m n s t
  have hint : ∀ (T : SchwartzMap D ℂ →L[ℂ] ℂ) s, Integrable (fun t => T (f s t)) μ₂ := fun T s => by
    obtain ⟨b, hbi, hbb⟩ := hTb T
    exact hbi.mono' (hwt s T).aestronglyMeasurable (ae_of_all _ fun t => hbb s t)
  have hGc : ∀ T : SchwartzMap D ℂ →L[ℂ] ℂ, Continuous fun s => T (G s) := by
    intro T
    obtain ⟨b, hbi, hbb⟩ := hTb T
    simp_rw [hTG _ T]
    exact continuous_of_dominated (fun s => (hwt s T).aestronglyMeasurable) (fun s => ae_of_all _ fun t => hbb s t) hbi
      (ae_of_all _ fun t => (hw T).comp (continuous_id.prodMk continuous_const))
  have hGb : ∀ m n : ℕ, ∃ c' : S₁ → ℝ, Integrable c' μ₁ ∧ ∀ s, SchwartzMap.seminorm ℂ m n (G s) ≤ c' s :=
    fun m n => ⟨fun _ => ∫ t, c m n t ∂μ₂, integrable_const _, fun s => hG2 s m n⟩
  have hGcont : Continuous G :=
    GlobalTheory.T.schwartz_continuous_of_seminorm_bounds G (GlobalTheory.T.weak_continuity_derivative_continuous G hGc) (fun m n => ⟨fun _ => ∫ t, c m n t ∂μ₂, continuous_const, fun s => hG2 s m n⟩)
  obtain ⟨F, -, hF1, -⟩ := GlobalTheory.T.schwartz_integral_of_integrable_bounds μ₁ G (fun n x => (GlobalTheory.T.weak_continuity_derivative_continuous G hGc n x).aestronglyMeasurable) hGb
  refine ⟨F, fun T => ⟨hint T, ?_, ?_⟩⟩
  · have e : (fun s => ∫ t, T (f s t) ∂μ₂) = fun s => T (G s) := funext fun s => (hTG s T).symm
    rw [e]
    obtain ⟨b, hbi, hbb⟩ := hTb T
    refine (integrable_const (∫ t, b t ∂μ₂)).mono' (hGc T).aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [hTG s T]
    exact norm_integral_le_of_norm_le hbi (ae_of_all _ fun t => hbb s t)
  · rw [GlobalTheory.T.schwartz_integral_eq_of_bounds μ₁ G F hGcont hGb hF1 T]
    exact integral_congr_ae (ae_of_all _ fun s => hTG s T)

theorem adm_integral_comm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (S₁ S₂ : Type) [TopologicalSpace S₁] [SecondCountableTopology S₁]
    [MeasurableSpace S₁] [BorelSpace S₁] [TopologicalSpace S₂] [SecondCountableTopology S₂] [MeasurableSpace S₂] [BorelSpace S₂]
    (μ₁ : Measure S₁) (μ₂ : Measure S₂) [IsFiniteMeasure μ₁] (r : ℕ) (g : Fin r → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : Fin r → S₁ → S₂ → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ j, g j ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ j (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ), Continuous (fun p : S₁ × S₂ => T (f j p.1 p.2))) →
    (∀ j (m n : ℕ), ∃ c : S₂ → ℝ, Continuous c ∧ Integrable c μ₂ ∧ ∀ s t, SchwartzMap.seminorm ℂ m n (f j s t) ≤ c t) →
    ∀ L ∈ (adeleClass F).adm κ,
      L (fun y => ∫ s, ∫ t, ∑ j, pureA F (f j s t) (g j) y ∂μ₂ ∂μ₁) = ∫ s, ∫ t, L (∑ j, pureA F (f j s t) (g j)) ∂μ₂ ∂μ₁ := by
  intro F _ _ κ _ S₁ S₂ _ _ _ _ _ _ _ _ μ₁ μ₂ _ r g f hg hc hd L hL
  choose Fj hFj using fun j => exists_iterated_integral_comm μ₁ μ₂ (f j) (hc j) (hd j)
  choose T hT using fun j => hL (g j) (hg j)
  have hpt : (fun y => ∫ s, ∫ t, ∑ j, pureA F (f j s t) (g j) y ∂μ₂ ∂μ₁) = ∑ j, pureA F (Fj j) (g j) := by
    funext y
    rw [Finset.sum_apply]
    simp only [pureA]
    set a := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1
    set b := fun i => (y i).2
    have hi : ∀ j s, Integrable (fun t => f j s t a * g j b) μ₂ := fun j s =>
      ((hFj j (evalAt a)).1 s).mul_const _
    have ho : ∀ j, Integrable (fun s => (∫ t, f j s t a ∂μ₂) * g j b) μ₁ := fun j =>
      (hFj j (evalAt a)).2.1.mul_const _
    have e1 : ∀ s, ∫ t, ∑ j, f j s t a * g j b ∂μ₂ = ∑ j, (∫ t, f j s t a ∂μ₂) * g j b := fun s => by
      rw [integral_finset_sum _ fun j _ => hi j s]
      exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
    simp_rw [e1]
    rw [integral_finset_sum _ fun j _ => ho j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
    congr 1
    exact ((hFj j (evalAt a)).2.2).symm
  rw [hpt, map_sum]
  have e2 : ∀ s t, L (∑ j, pureA F (f j s t) (g j)) = ∑ j, T j (f j s t) := fun s t => by
    rw [map_sum]; exact Finset.sum_congr rfl fun j _ => hT j _
  simp_rw [e2]
  have e3 : ∀ s, ∫ t, ∑ j, T j (f j s t) ∂μ₂ = ∑ j, ∫ t, T j (f j s t) ∂μ₂ := fun s =>
    integral_finset_sum _ fun j _ => (hFj j (T j)).1 s
  simp_rw [e3]
  rw [integral_finset_sum _ fun j _ => (hFj j (T j)).2.1]
  exact Finset.sum_congr rfl fun j _ => by rw [hT j]; exact (hFj j (T j)).2.2

end GlobalTheory.AdmInt

end
