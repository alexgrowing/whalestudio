import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RestrSchA

variable {κ₁ κ : Type} {j : κ₁ → κ}

theorem extend_map {M N : Type} [Zero M] [Zero N] (hj : Function.Injective j) (φ : M → N) (h0 : φ 0 = 0)
    (y : κ₁ → M) : (fun i => φ (Function.extend j y 0 i)) = Function.extend j (fun a => φ (y a)) 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h, h0]

theorem extend_add {M : Type} [AddZeroClass M] (hj : Function.Injective j) (y z : κ₁ → M) :
    Function.extend j (y + z) 0 = Function.extend j y 0 + Function.extend j z 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem extend_smul {R M : Type} [Zero M] [SMulZeroClass R M] (hj : Function.Injective j) (c : R) (y : κ₁ → M) :
    Function.extend j (c • y) 0 = c • Function.extend j y 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem continuous_extend {M : Type} [TopologicalSpace M] [Zero M] (hj : Function.Injective j) :
    Continuous (fun y : κ₁ → M => Function.extend j y 0) := by
  refine continuous_pi fun i => ?_
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp only [hj.extend_apply]
    exact continuous_apply a
  · simp only [Function.extend_apply' _ _ _ h]
    exact continuous_const

theorem isClosedEmbedding_extend {M : Type} [TopologicalSpace M] [Zero M] [T2Space M] (hj : Function.Injective j) :
    Topology.IsClosedEmbedding (fun y : κ₁ → M => Function.extend j y 0) :=
  Function.LeftInverse.isClosedEmbedding (f := fun x : κ → M => x ∘ j)
    (fun y => by funext a; simp [hj.extend_apply]) (by fun_prop) (continuous_extend hj)

end GlobalTheory.RestrSchA

namespace GlobalTheory.RestrSchA

open scoped Classical

variable {κ₁ κ : Type} {j : κ₁ → κ}

def extL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (hj : Function.Injective j) :
    (κ₁ → V) →L[ℝ] (κ → V) where
  toFun y := Function.extend j y 0
  map_add' y z := extend_add hj y z
  map_smul' c y := extend_smul hj c y
  cont := continuous_extend hj

theorem norm_le_extL {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype κ₁] [Fintype κ]
    (hj : Function.Injective j) (y : κ₁ → V) : ‖y‖ ≤ ‖extL V hj y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  have h : extL V hj y (j a) = y a := by simp [extL, hj.extend_apply]
  rw [← h]
  exact norm_le_pi_norm _ _

def restrS (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j) :
    SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ₁ → NumberField.mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLM ℂ (extL (NumberField.mixedEmbedding.mixedSpace F) hj).hasTemperateGrowth
    ⟨1, 1, fun y => by
      have := norm_le_extL hj y
      have h0 := norm_nonneg (extL (NumberField.mixedEmbedding.mixedSpace F) hj y)
      simp only [pow_one, one_mul]
      linarith⟩

theorem restrS_apply (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (y : κ₁ → NumberField.mixedEmbedding.mixedSpace F) :
    restrS F hj f y = f (Function.extend j y 0) := by
  simp [restrS, extL]

theorem sb_comp_extend (F : Type) [Field F] [NumberField F] (hj : Function.Injective j)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y => g (Function.extend j y 0)) ∈ SB (κ₁ → FiniteAdeleRing (𝓞 F) F) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite))
  exact ⟨hg.1.comp_continuous (continuous_extend hj), hg.2.comp_isClosedEmbedding (isClosedEmbedding_extend hj)⟩

theorem pureA_extend (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ₁ → AdeleRing (𝓞 F) F) :
    pureA F f g (Function.extend j y 0) = pureA F (restrS F hj f) (fun z => g (Function.extend j z 0)) y := by
  simp only [pureA, restrS_apply]
  rw [extend_map hj (fun x : AdeleRing (𝓞 F) F => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
      (by show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0; exact map_zero _) y,
    extend_map hj (fun x : AdeleRing (𝓞 F) F => x.2) rfl y]

theorem mem_schA_comp_extend : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ Φ ∈ schA F κ, (fun y => Φ (Function.extend j y 0)) ∈ schA F κ₁ := by
  intro F _ _ κ₁ κ _ _ j hj Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨restrS F hj f, fun z => g (Function.extend j z 0), sb_comp_extend F hj hg, ?_⟩
    funext y
    exact pureA_extend F hj f g y
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.RestrSchA

end
