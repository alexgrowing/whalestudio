import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Mathlib.Topology.Algebra.ClopenNhdofOne

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_open_normal {P Z : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    [TotallyDisconnectedSpace P] (K : Subgroup P) (hK : IsOpen (K : Set P)) (c : K → Z) (hc : IsLocallyConstant c) :
    ∃ V : OpenNormalSubgroup P, ∀ g g' : K, (g : P)⁻¹ * g' ∈ V → c g = c g' := by
  have hKc : IsClosed (K : Set P) := Subgroup.isClosed_of_isOpen K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  have hfin : (Set.range c).Finite := hc.range_finite
  have hS : ∀ z, ∃ W ∈ nhds (1 : P), ∀ x ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P), ∀ w ∈ W,
      x * w ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P) := by
    intro z
    have hcpt : IsCompact (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
      (hc.isClosed_fiber z).isCompact.image continuous_subtype_val
    have ho : IsOpen (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
      hK.isOpenMap_subtype_val _ (hc.isOpen_fiber z)
    open scoped Pointwise in
    obtain ⟨W, hW, hWS⟩ := compact_open_separated_mul_right hcpt ho subset_rfl
    open scoped Pointwise in
    exact ⟨W, hW, fun x hx w hw => hWS (Set.mul_mem_mul hx hw)⟩
  choose W hW hWS using hS
  have hI : (⋂ z ∈ Set.range c, W z) ∈ nhds (1 : P) := (Filter.biInter_mem hfin).2 fun z _ => hW z
  obtain ⟨O, hOI, hOo, h1O⟩ := mem_nhds_iff.1 hI
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  refine ⟨H, fun g g' hgg => ?_⟩
  have h1 : (g : P)⁻¹ * g' ∈ W (c g) := Set.mem_iInter₂.1 (hOI (hH hgg)) (c g) ⟨g, rfl⟩
  have h2 : (g : P) ∈ Subtype.val '' (c ⁻¹' {c g}) := ⟨g, rfl, rfl⟩
  have h3 := hWS (c g) _ h2 _ h1
  rw [mul_inv_cancel_left] at h3
  obtain ⟨a', ha', he⟩ := h3
  have e : a' = g' := Subtype.ext he
  rw [← e]
  exact ha'.symm

theorem UpperTheory.V.Pa.eventually_factorization_compatible_with_local_maps :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (c : Λ.Ph0 → Z), IsLocallyConstant c → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ (zN : (T.GN N).G₀ → Z) (z : Λ.G.G₀ → Z), (∀ g, zN (Λ.π0 N g) = c g) → (∀ g, z (Λ.πo0 g) = c g) → (∀ v g, zN ((T.GN N).φ v g) = z (Λ.G.φ v g)) ∧ (∀ w g, zN ((T.GN N).φu w g) = z (Λ.G.φu w g)) ∧ ∀ j, zN (T.ph N j) = z (Λ.ph j) ∧ zN (T.ta N j) = z (Λ.ta j) := by
  intro l _ L G0 T Λ Z c hc
  obtain ⟨V, hV⟩ := exists_open_normal _ Λ.Ph0_open c hc
  filter_upwards [Λ.φ_lim V, Λ.φu_lim V, Λ.ph_lim V, Λ.ta_lim V] with N h1 h2 h3 h4 zN z hN ho
  have key : ∀ (a : (T.GN N).G₀) (b : Λ.G.G₀), Close (Λ.π N) Λ.πo V.toSubgroup (a : (T.GN N).Γ) (b : Λ.G.Γ) →
      zN a = z b := by
    rintro a b ⟨g, g', ea, eb, hg⟩
    have m : g ∈ (Λ.G.η.comp Λ.πo).ker := (Λ.η_π N g).symm.trans (by rw [ea]; exact a.2)
    have m' : g' ∈ (Λ.G.η.comp Λ.πo).ker := show Λ.G.η (Λ.πo g') = 1 by rw [eb]; exact b.2
    have ea' : a = Λ.π0 N ⟨g, m⟩ := Subtype.ext ea.symm
    have eb' : b = Λ.πo0 ⟨g', m'⟩ := Subtype.ext eb.symm
    rw [ea', eb', hN, ho]
    exact hV _ _ hg
  exact ⟨fun v g => key _ _ (h1 v g), fun w g => key _ _ (h2 w g), fun j => ⟨key _ _ (h3 j), key _ _ (h4 j)⟩⟩
