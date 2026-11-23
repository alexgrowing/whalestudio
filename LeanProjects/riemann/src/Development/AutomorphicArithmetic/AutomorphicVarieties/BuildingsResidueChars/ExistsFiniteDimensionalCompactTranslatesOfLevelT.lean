import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsOpenLevelNormalizedByIntegralFiniteGL

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_finiteDimensional_compact_translates_of_level_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Level S → Types S → ∃ V : Submodule ℂ (Reduction.maxCompact (K := K) (n := n) → ℂ), FiniteDimensional ℂ V ∧ ∀ φ ∈ S, ∀ g, (fun k : Reduction.maxCompact (K := K) (n := n) => φ.1 (g * k.1)) ∈ V := by
  intro K _ _ n S hLev hTyp
  obtain ⟨L, hL, hinv⟩ := hLev
  obtain ⟨V₀, hV₀, -, hφV⟩ := hTyp
  obtain ⟨L', -, hL'L, -, t, ht⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL K n L hL
  have hk : ∀ k : Reduction.maxCompact (K := K) (n := n), ∃ c ∈ t, c⁻¹ * finPart k.1 ∈ L' :=
    fun k => ht _ (finPart_mem_integralFiniteGL k.2)
  let Ψ : (↥t → ↥V₀) →ₗ[ℂ] (Reduction.maxCompact (K := K) (n := n) → ℂ) :=
    { toFun := fun h k =>
        (h ⟨Classical.choose (hk k), (Classical.choose_spec (hk k)).1⟩ : archCompact K n → ℂ)
          ⟨archPart k.1, archPart_mem_archCompact k.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine ⟨LinearMap.range Ψ, inferInstance, ?_⟩
  intro φ hφ g
  refine ⟨fun c => ⟨fun k' => φ.1 (g * finEmb K n c.1 * infEmb K n k'.1), hφV φ hφ _⟩, ?_⟩
  funext k
  show φ.1 (g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1)) = φ.1 (g * k.1)
  have hu : (Classical.choose (hk k))⁻¹ * finPart k.1 ∈ L := hL'L (Classical.choose_spec (hk k)).2
  have e : g * k.1 = g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1) *
      finEmb K n ((Classical.choose (hk k))⁻¹ * finPart k.1) := by
    conv_lhs => rw [← infEmb_archPart_mul_finEmb_finPart k.1]
    rw [map_mul, map_inv, mul_assoc g (finEmb K n _), ← infEmb_mul_finEmb_comm]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [e, hinv φ hφ _ hu]
