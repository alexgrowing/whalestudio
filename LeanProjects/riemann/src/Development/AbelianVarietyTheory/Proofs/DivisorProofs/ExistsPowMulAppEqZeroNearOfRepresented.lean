import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

private theorem app_comp_ι_eq_zero_iff {T S : Scheme.{0}} (U : S.Opens) (g : T ⟶ U) (V : U.toScheme.Opens) (x : Γ(S, U.ι ''ᵁ V)) :
    ((g ≫ U.ι).app (U.ι ''ᵁ V)).hom x = 0 ↔ (g.app V).hom x = 0 := by
  have e : (g ≫ U.ι).app (U.ι ''ᵁ V) = g.app V ≫ T.presheaf.map (eqToHom (by simp)).op := by
    simp only [Scheme.Hom.comp_app, Scheme.Opens.ι_app]
    refine (g.naturality (homOfLE (U.ι.preimage_image_eq V).le).op).trans ?_
    congr 2
  rw [e]
  exact map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1

private theorem restrict_app_eq_zero_iff {T S : Scheme.{0}} (f : T ⟶ S) (U : S.Opens) (V : U.toScheme.Opens) (a : Γ(S, U.ι ''ᵁ V)) :
    ((f ∣_ U).app V).hom a = 0 ↔ (f.app (U.ι ''ᵁ V)).hom a = 0 := by
  rw [morphismRestrict_app]
  exact map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1

private theorem app_res_eq_zero {S T : Scheme.{0}} (t : T ⟶ S) {V W : S.Opens} (h : V ≤ W) (b : Γ(S, W))
    (hb : (t.app W).hom b = 0) : (t.app V).hom ((S.presheaf.map (homOfLE h).op).hom b) = 0 := by
  have e := congrArg (fun φ => φ.hom b) (t.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e, hb, map_zero]

theorem exists_pow_mul_app_eq_zero_near_of_represented : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → ∀ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), IsClosedImmersion i → (∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∀ (W : S.Opens) (s c : Γ(S, W)), (∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app (S.basicOpen s)).hom ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) = 0) → ∀ y : S, y ∈ U → y ∈ W → ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
  intro S Φ hstab U Z i hi hrep W s c hc y hyU hyW
  have hm : (⟨y, hyU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ W := hyW
  obtain ⟨V', hV'aff, hyV', hV'le⟩ := (Opens.isBasis_iff_nbhd.mp U.toScheme.isBasis_affineOpens) hm
  have hV : U.ι ''ᵁ V' ≤ W := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hx
    exact hV'le hx'
  refine ⟨U.ι ''ᵁ V', hV, ⟨⟨y, hyU⟩, hyV', rfl⟩, ?_⟩
  set V : S.Opens := U.ι ''ᵁ V' with hVdef
  set p : Z ⟶ S := i ≫ U.ι with hpdef
  let cV : Γ(S, V) := (S.presheaf.map (homOfLE hV).op).hom c
  let sV : Γ(S, V) := (S.presheaf.map (homOfLE hV).op).hom s
  have hpre : p ⁻¹ᵁ V = i ⁻¹ᵁ V' := by
    rw [hpdef, Scheme.Hom.comp_preimage, hVdef, U.ι.preimage_image_eq V']
  have hcpt : IsCompact ((p ⁻¹ᵁ V : Z.Opens) : Set Z) := by
    rw [hpre]
    exact QuasiCompact.isCompact_preimage (f := i) _ V'.2 hV'aff.isCompact
  have hΦi : Φ Z p := (hrep Z i).2 ⟨𝟙 _, Category.id_comp _⟩
  have h0 := hc Z p hΦi
  have h1 := app_res_eq_zero p (inf_le_right : V ⊓ S.basicOpen s ≤ S.basicOpen s) _ h0
  have hres : (S.presheaf.map (homOfLE (inf_le_left : V ⊓ S.basicOpen s ≤ V)).op).hom cV =
      (S.presheaf.map (homOfLE (inf_le_right : V ⊓ S.basicOpen s ≤ S.basicOpen s)).op).hom
        ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) := by
    simp only [cV, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have key : ∀ (O : Z.Opens) (_ : O = p ⁻¹ᵁ (V ⊓ S.basicOpen s)) (h : O ≤ p ⁻¹ᵁ V),
      (Z.presheaf.map (homOfLE h).op).hom ((p.app V).hom cV) = 0 := by
    rintro O rfl h
    have e := congrArg (fun φ => φ.hom cV) (p.naturality (homOfLE (inf_le_left : V ⊓ S.basicOpen s ≤ V)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    refine e.symm.trans ?_
    rw [hres]
    exact h1
  have hO : Z.basicOpen ((p.app V).hom sV) = p ⁻¹ᵁ (V ⊓ S.basicOpen s) := by
    rw [← Scheme.preimage_basicOpen, Scheme.basicOpen_res]
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Z hcpt
    ((p.app V).hom cV) ((p.app V).hom sV) (key _ hO _)
  have hpa : (p.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
    rw [map_mul, map_pow, map_mul, map_pow]
    exact hn
  have hia := (app_comp_ι_eq_zero_iff U i V' _).1 hpa
  refine ⟨n, fun T t ht => ?_⟩
  have ht' : Φ _ ((t ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    exact hstab _ _ t _ ht
  obtain ⟨z, hz⟩ := (hrep _ (t ∣_ U)).1 ht'
  refine (restrict_app_eq_zero_iff t U V' _).1 ?_
  rw [← hz, Scheme.Hom.comp_app]
  exact (congrArg (fun x => (z.app (i ⁻¹ᵁ V')).hom x) hia).trans (map_zero _)
end GlobalTheory
