import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual

namespace GlobalTheory.SmGL.IndCoinv

variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}

theorem smIndMap_bump (β : σ.IntertwiningMap ρ) {J : Subgroup G} (hJ : IsOpen (J : Set G))
    (w : fixed σ (J.subgroupOf P)) (v : fixed ρ (J.subgroupOf P)) (hv : β w = v) :
    smIndMap β (bump σ hJ w) = bump ρ hJ v := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  show β ((bump σ hJ w).1.1 g) = _
  rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
  · rw [bump_zero _ _ _ h, bump_zero _ _ _ h, map_zero]
  · rw [bump_mul _ _ _ _ hj, bump_mul _ _ _ _ hj, β.isIntertwining, hv]

theorem mem_of_bump {K : Subgroup G} (hK : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hb : ∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (Z : Submodule ℂ (smoothPart (ind P σ))) (hZ : ∀ g, ∀ f ∈ Z, smInd P σ g f ∈ Z)
    (h : ∀ (J : Subgroup G) (hJ : IsOpen (J : Set G)), J ≤ K → ∀ w, bump σ hJ w ∈ Z)
    (f : smoothPart (ind P σ)) : f ∈ Z := by
  obtain ⟨J, hJ, hJU, hle, hn⟩ := hb _ (IsOpen.mem_nhds (isSmooth_smoothRep _ f) (by
    rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply]))
  refine Submodule.span_le.2 ?_ (mem_span_bump σ hJ hK hle hn hPK f fun j hj => hJU hj)
  rintro _ ⟨z, -, w, rfl⟩
  exact hZ _ _ (h J hJ hle w)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem map_mem_fixed {σ : Representation ℂ G X} {ρ : Representation ℂ G U} (β : σ.IntertwiningMap ρ)
    {H : Subgroup G} {w : X} (hw : w ∈ fixed σ H) : β w ∈ fixed ρ H :=
  mem_fixed_iff.2 fun h hh => by rw [← β.isIntertwining, mem_fixed_iff.1 hw h hh]

theorem mem_of_fixed [T2Space G] {σ : Representation ℂ G X} (hσ : IsSmooth σ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {Γ : Type} (T : Γ → σ.IntertwiningMap σ) (M : Submodule ℂ (fixed σ H))
    (hM : ∀ γ (z : fixed σ H), (⟨T γ z, map_mem_fixed (T γ) z.2⟩ : fixed σ H) - z ∈ M) (w : fixed σ H)
    (hw : w.1 ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) : w ∈ M := by
  by_contra hn
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend l
  obtain ⟨l₁, h1, h2⟩ := GlobalTheory.SmGL.DualAverage.exists_invariant_form G X σ hσ _ hH l₀
  have h3 : ∀ v : fixed σ H, l₁ v = l v := fun v =>
    (h2 _ (mem_fixed_iff.1 v.2)).trans (LinearMap.congr_fun hl₀ v)
  have h4 : ∀ γ, l₁ ∘ₗ (T γ).toLinearMap = l₁ := fun γ =>
    dual_ext hσ hH (fun h hh v => by
      show l₁ (T γ _) = l₁ (T γ _)
      rw [(T γ).isIntertwining, h1 h hh]) h1 fun v hv => by
      have h5 : l (_ - _) ∈ M.map l := Submodule.mem_map_of_mem (hM γ ⟨v, hv⟩)
      rw [hl0, Submodule.mem_bot, map_sub, ← h3, ← h3, sub_eq_zero] at h5
      exact h5
  apply hl
  rw [← h3]
  refine (Submodule.span_le (p := LinearMap.ker l₁)).2 ?_ hw
  rintro _ ⟨γ, z, rfl⟩
  have h5 : l₁ (T γ z) = l₁ z := LinearMap.congr_fun (h4 γ) z
  simp [h5]

theorem smInd_coinvariants : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (P K : Subgroup G), IsClosed (P : Set G) → IsCompact (K : Set G) → (∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x) → (∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧ ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (U : Type) [AddCommGroup U] [Module ℂ U] (σ : Representation ℂ P X) (ρ : Representation ℂ P U), IsSmooth σ → ∀ (α : σ.IntertwiningMap ρ) (Γ : Type) (T : Γ → σ.IntertwiningMap σ), Function.Surjective α → (∀ x, α x = 0 → x ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) → Function.Surjective (smIndMap α) ∧ ∀ f, smIndMap α f = 0 → f ∈ Submodule.span ℂ {y : smoothPart (ind P σ) | ∃ γ z, y = smIndMap (T γ) z - z} := by
  intro G _ _ _ _ P K hP hK hPK hb X _ _ U _ _ σ ρ hσ α Γ T hα hker
  have hc : ∀ J : Subgroup G, IsOpen (J : Set G) → J ≤ K → IsCompact (J.subgroupOf P : Set P) :=
    fun J hJ hle => hP.isClosedEmbedding_subtypeVal.isCompact_preimage
      (hK.of_isClosed_subset (J.isClosed_of_isOpen hJ) hle)
  constructor
  · intro f
    refine mem_of_bump hK hPK hb (LinearMap.range (smIndMap α).toLinearMap) ?_ ?_ f
    · rintro g _ ⟨φ, rfl⟩
      exact ⟨smInd P σ g φ, rfl⟩
    · intro J hJ hle w
      obtain ⟨x, hx⟩ := hα w
      obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hσ (hc J hJ hle) α.toLinearMap x fun h hh => by
        show α _ = α _
        rw [α.isIntertwining, hx, mem_fixed_iff.1 w.2 h hh]
      exact ⟨bump σ hJ ⟨v, hv⟩, smIndMap_bump α hJ _ _ (e.trans hx)⟩
  · intro f hf
    set Z := Submodule.span ℂ {y : smoothPart (ind P σ) | ∃ γ z, y = smIndMap (T γ) z - z} with hZ
    let N : Submodule ℂ X := LinearMap.ker α.toLinearMap
    have hN : ∀ g, ∀ v ∈ N, σ g v ∈ N := fun g v hv => by
      have hv' : α v = 0 := hv
      show α _ = 0
      rw [α.isIntertwining, hv', map_zero]
    let τ := sub σ N hN
    let j : τ.IntertwiningMap σ := { toLinearMap := N.subtype, isIntertwining' := fun _ => rfl }
    let f' : smoothPart (ind P τ) :=
      ⟨⟨fun g => ⟨f.1.1 g, congrArg (fun φ : smoothPart (ind P ρ) => φ.1.1 g) hf⟩, fun h g => Subtype.ext (f.1.2 h g)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
          have hg' : ind P σ g f.1 = f.1 := hg
          exact Subtype.ext (funext fun x => Subtype.ext (congrFun (congrArg Subtype.val hg') x)))⟩
    have hst : ∀ g, Z ≤ Z.comap (smInd P σ g) := fun g => Submodule.span_le.2 (by
      rintro _ ⟨γ, z, rfl⟩
      exact Submodule.subset_span ⟨γ, smInd P σ g z, rfl⟩)
    refine mem_of_bump hK hPK hb (Z.comap (smIndMap j).toLinearMap) (fun g φ hφ => hst g hφ) ?_ f'
    intro J hJ hle w
    have hw := map_mem_fixed j w.2
    show smIndMap j _ ∈ Z
    rw [smIndMap_bump j hJ w ⟨_, hw⟩ rfl]
    refine mem_of_fixed hσ (hc J hJ hle) T (Z.comap (bump σ hJ)) (fun γ z => ?_) _ (hker _ w.1.2)
    rw [Submodule.mem_comap, map_sub, ← smIndMap_bump (T γ) hJ z _ rfl]
    exact Submodule.subset_span ⟨γ, _, rfl⟩

end GlobalTheory.SmGL.IndCoinv
