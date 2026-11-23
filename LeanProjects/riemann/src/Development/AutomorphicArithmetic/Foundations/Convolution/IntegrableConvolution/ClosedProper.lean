import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

open Topology

private theorem UpperTheory.ConvolutionTheory.L1.compact_lift {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] {f : X → Y} (hf : IsOpenMap f) (hs : Function.Surjective f) {D : Set Y}
    (hD : IsCompact D) : ∃ K : Set X, IsCompact K ∧ D ⊆ f '' K := by
  have h : ∀ z : Y, ∃ K : Set X, IsCompact K ∧ f '' K ∈ 𝓝 z := by
    intro z
    obtain ⟨g, rfl⟩ := hs z
    obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
    exact ⟨K, hK, hf.image_mem_nhds hg⟩
  choose K hK hK' using h
  obtain ⟨t, -, ht⟩ := hD.elim_nhds_subcover (fun z => f '' K z) (fun z _ => hK' z)
  refine ⟨⋃ z ∈ t, K z, t.isCompact_biUnion fun z _ => hK z, ?_⟩
  intro y hy
  obtain ⟨z, hz, g, hg, rfl⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact ⟨g, Set.mem_iUnion₂.2 ⟨z, hz, hg⟩, rfl⟩

theorem UpperTheory.ConvolutionTheory.L1.closedProper :
    UpperTheory.ConvolutionTheory.L1.ClosedProper := by
  intro G _ _ _ _ _ _ γ hO D hD
  set O : Set G := {y | ∃ x, y = x⁻¹ * γ * x} with hOdef
  letI : MulAction G O :=
    { smul := fun g y => ⟨g * y.1 * g⁻¹, by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨x * g⁻¹, by rw [hx]; group⟩⟩
      one_smul := fun y => Subtype.ext (by change 1 * y.1 * 1⁻¹ = y.1; group)
      mul_smul := fun a b y => Subtype.ext (by
        change a * b * y.1 * (a * b)⁻¹ = a * (b * y.1 * b⁻¹) * a⁻¹; group) }
  have hsm : ∀ (g : G) (y : O), ((g • y : O) : G) = g * y.1 * g⁻¹ := fun _ _ => rfl
  haveI : ContinuousSMul G O := ⟨by
    refine continuous_induced_rng.2 ?_
    change Continuous fun p : G × O => p.1 * p.2.1 * p.1⁻¹
    fun_prop⟩
  haveI : MulAction.IsPretransitive G O := ⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact ⟨b⁻¹ * a, Subtype.ext (by rw [hsm]; group)⟩⟩
  haveI : LocallyCompactSpace O := hO.locallyCompactSpace
  let γ₀ : O := ⟨γ, 1, by group⟩
  have hopen : IsOpenMap (fun g : G => g • γ₀) := isOpenMap_smul_of_sigmaCompact γ₀
  have hsurj : Function.Surjective (fun g : G => g • γ₀) := fun y => MulAction.exists_smul_eq G γ₀ y
  have hD' : IsCompact (Subtype.val ⁻¹' D : Set O) := hO.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  obtain ⟨K, hK, hDK⟩ := UpperTheory.ConvolutionTheory.L1.compact_lift hopen hsurj hD'
  refine ⟨K⁻¹, hK.inv, fun x hx => ?_⟩
  obtain ⟨g, hg, hgx⟩ := hDK (a := ⟨x⁻¹ * γ * x, x, rfl⟩) hx
  have h1 : g * γ * g⁻¹ = x⁻¹ * γ * x := congrArg Subtype.val hgx
  refine ⟨x * g, ?_, g⁻¹, by simpa using hg, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro h rfl
  calc h * (x * g) = x * (x⁻¹ * h * x) * g := by group
    _ = x * (g * h * g⁻¹) * g := by rw [h1]
    _ = x * g * h := by group
