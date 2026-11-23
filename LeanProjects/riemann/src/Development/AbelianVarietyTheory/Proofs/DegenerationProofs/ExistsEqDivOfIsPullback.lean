import Mathlib

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.SS

theorem exists_eq_div_of_isPullback : ∀ (P X Y S : Scheme.{0}) [IsAffine S] (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S), IsPullback p q f g → ∀ (z : P) (U : X.Opens) (U' : Y.Opens) (W : P.Opens), p z ∈ U → q z ∈ U' → z ∈ W → ∃ (V : X.Opens) (V' : Y.Opens) (W' : P.Opens) (h₁ : W' ≤ p ⁻¹ᵁ V) (h₂ : W' ≤ q ⁻¹ᵁ V'), V ≤ U ∧ V' ≤ U' ∧ W' ≤ W ∧ z ∈ W' ∧ ∀ τ : Γ(P, W'), ∃ a ∈ Subring.closure (Set.range (p.appLE V W' h₁).hom ∪ Set.range (q.appLE V' W' h₂).hom), ∃ b ∈ Subring.closure (Set.range (p.appLE V W' h₁).hom ∪ Set.range (q.appLE V' W' h₂).hom), IsUnit a ∧ τ * a = b := by
  intro P X Y S _ p q f g H z U U' W hU hU' hW
  obtain ⟨V, hV, hpV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) hU
  obtain ⟨V', hV', hpV', hVU'⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := U') hU'
  have hP : IsAffineOpen (p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ V') := by
    have : IsAffine _ := hV
    have : IsAffine _ := hV'
    have : IsAffine _ := isAffineOpen_top S
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V') (UX := V) le_top le_top
      rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V') (UX := V) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hV' hV)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  obtain ⟨r, hrW, hzr⟩ := hP.exists_basicOpen_le (V := W) ⟨z, hW⟩ ⟨hpV, hpV'⟩
  have hle : P.basicOpen r ≤ p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ V' := P.basicOpen_le r
  refine ⟨V, V', P.basicOpen r, hle.trans inf_le_left, hle.trans inf_le_right, hVU, hVU', hrW,
    hzr, fun τ => ?_⟩
  have key : ∀ x : Γ(P, p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ V'), (P.presheaf.map (homOfLE hle).op).hom x ∈
      Subring.closure (Set.range (p.appLE V _ (hle.trans inf_le_left)).hom ∪
        Set.range (q.appLE V' _ (hle.trans inf_le_right)).hom) := by
    intro x
    have hx := hgen.ge (Subring.mem_top x)
    refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ hx)
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    · refine Subring.subset_closure (Or.inr ⟨a, ?_⟩)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hloc := hP.isLocalization_basicOpen r
  obtain ⟨⟨b, a⟩, hab⟩ := IsLocalization.surj (Submonoid.powers r) τ
  exact ⟨_, key a, _, key b, IsLocalization.map_units Γ(P, P.basicOpen r) a, hab⟩

end GlobalTheory.SS
