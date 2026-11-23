import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Mathlib.Topology.Algebra.ClopenNhdofOne

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.eventually_locallyConstant_comp_tower_eq :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (ρ : G0.G₀ → Z), IsLocallyConstant ρ → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ g, ρ ((T.h N).p₀ (Λ.π0 N g)) = ρ (Λ.h.p₀ (Λ.πo0 g)) := by
  intro l _ L G0 T Λ Z ρ hρ
  have hKo : IsOpen ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := G0.η_open
  have hKc : IsClosed ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := Subgroup.isClosed_of_isOpen _ hKo
  haveI : CompactSpace G0.G₀ := isCompact_iff_compactSpace.mp hKc.isCompact
  have hfin : (Set.range ρ).Finite := hρ.range_finite
  have hS : ∀ z, ∃ V ∈ nhds (1 : G0.Γ), ∀ v ∈ V, ∀ x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ),
      v * x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) := by
    intro z
    have hc : IsCompact (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
      (hρ.isClosed_fiber z).isCompact.image continuous_subtype_val
    have ho : IsOpen (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
      hKo.isOpenMap_subtype_val _ (hρ.isOpen_fiber z)
    open scoped Pointwise in
    obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hc ho subset_rfl
    open scoped Pointwise in
    exact ⟨V, hV, fun v hv x hx => hVS (Set.mul_mem_mul hv hx)⟩
  choose V hV hVS using hS
  have hW : (⋂ z ∈ Set.range ρ, V z) ∈ nhds (1 : G0.Γ) := (Filter.biInter_mem hfin).2 fun z _ => hV z
  obtain ⟨O, hOW, hOo, h1O⟩ := mem_nhds_iff.1 hW
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  filter_upwards [Λ.p_lim H] with N hN g
  set a := (T.h N).p₀ (Λ.π0 N g)
  set b := Λ.h.p₀ (Λ.πo0 g)
  have hab : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ (H : Set G0.Γ) := hN g.1
  have h1 : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ V (ρ b) := Set.mem_iInter₂.1 (hOW (hH hab)) (ρ b) ⟨b, rfl⟩
  have h2 : (b : G0.Γ) ∈ Subtype.val '' (ρ ⁻¹' {ρ b}) := ⟨b, rfl, rfl⟩
  have h3 := hVS (ρ b) _ h1 _ h2
  rw [inv_mul_cancel_right] at h3
  obtain ⟨a', ha', he⟩ := h3
  have e : a' = a := Subtype.ext he
  rw [← e]
  exact ha'
