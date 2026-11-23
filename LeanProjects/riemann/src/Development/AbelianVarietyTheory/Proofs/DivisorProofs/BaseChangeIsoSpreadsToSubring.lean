import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismsEqSpreadToSubring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.IsoSpread

theorem spMap_inclusion_comp {S : Type} [CommRing S] {A B C : Subring S} (h₁ : A ≤ B)
    (h₂ : B ≤ C) :
    spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) =
      spMap (Subring.inclusion (h₁.trans h₂)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem spMap_subtype_comp {S : Type} [CommRing S] {A B : Subring S} (h : A ≤ B) :
    spMap B.subtype ≫ spMap (Subring.inclusion h) = spMap A.subtype := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_isPullback_lift {X₀ X₁ T₀ T₁ T₂ : Scheme.{0}} {f₀ : X₀ ⟶ T₀} {f₁ : X₁ ⟶ T₁}
    {π₁ : X₁ ⟶ X₀} {u : T₁ ⟶ T₂} {v : T₂ ⟶ T₀} {w : T₁ ⟶ T₀} (huv : u ≫ v = w)
    (hp : IsPullback π₁ f₁ f₀ w) :
    ∃ m : X₁ ⟶ pullback f₀ v, m ≫ pullback.fst _ _ = π₁ ∧ m ≫ pullback.snd _ _ = f₁ ≫ u ∧
      IsPullback m f₁ (pullback.snd f₀ v) u := by
  subst huv
  refine ⟨pullback.lift π₁ (f₁ ≫ u) (by rw [Category.assoc, hp.w]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst]
  exact hp

end GlobalTheory.IsoSpread

namespace GlobalTheory

open GlobalTheory.IsoSpread in

theorem iso_spreads_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀] [QuasiCompact q] [QuasiSeparated q] [LocallyOfFinitePresentation q] (φ : X ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → IsPullback φ f q (spMap R₀.subtype) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Z, j ≫ ψ = φ ∧ IsPullback ψ f₁ q (spMap (Subring.inclusion hle)) := by
  classical
  intro S _ R₀ X X₀ Z f f₀ q π _ _ _ _ _ _ φ hπ hφ

  obtain ⟨Fa, ha⟩ := morphism_descends_to_subring S R₀ X X₀ Z f f₀ q π φ hπ
    (hφ.w.trans hπ.w.symm)
  obtain ⟨Fb, hb⟩ := morphism_descends_to_subring S R₀ X Z X₀ f q f₀ φ π hφ
    (hπ.w.trans hφ.w.symm)

  let R₂ : Subring S := Subring.closure ((R₀ : Set S) ∪ (Fa : Set S) ∪ (Fb : Set S))
  have h₀₂ : R₀ ≤ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inl hx))
  have hFa : (Fa : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inr hx))
  have hFb : (Fb : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inr hx)
  obtain ⟨j₂, hj₂f, hj₂s, hj₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hπ
  obtain ⟨k₂, hk₂f, hk₂s, hk₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hφ
  obtain ⟨ψ₂, hψ₂, hψ₂q⟩ := ha R₂ h₀₂ hFa _ _ _ j₂ (IsPullback.of_hasPullback _ _) hj₂f hj₂s
  obtain ⟨χ₂, hχ₂, hχ₂q⟩ := hb R₂ h₀₂ hFb _ _ _ k₂ (IsPullback.of_hasPullback _ _) hk₂f hk₂s
  let α₂ := pullback.lift ψ₂ (pullback.snd f₀ (spMap (Subring.inclusion h₀₂)))
    (by rw [hψ₂q, pullback.condition])
  let β₂ := pullback.lift χ₂ (pullback.snd q (spMap (Subring.inclusion h₀₂)))
    (by rw [hχ₂q, pullback.condition])
  have hα₂f : α₂ ≫ pullback.fst _ _ = ψ₂ := pullback.lift_fst _ _ _
  have hα₂s : α₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hβ₂f : β₂ ≫ pullback.fst _ _ = χ₂ := pullback.lift_fst _ _ _
  have hβ₂s : β₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hjα : j₂ ≫ α₂ = k₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₂f, hψ₂, hk₂f]
    · rw [Category.assoc, hα₂s, hj₂s, hk₂s]
  have hkβ : k₂ ≫ β₂ = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hβ₂f, hχ₂, hj₂f]
    · rw [Category.assoc, hβ₂s, hj₂s, hk₂s]

  obtain ⟨Fc, hc⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ j₂ (α₂ ≫ β₂) (𝟙 _) hj₂
    (by rw [Category.assoc, hβ₂s, hα₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hjα, hkβ, Category.comp_id])
  obtain ⟨Fd, hd⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ k₂ (β₂ ≫ α₂) (𝟙 _) hk₂
    (by rw [Category.assoc, hα₂s, hβ₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hkβ, hjα, Category.comp_id])
  refine ⟨Fa ∪ Fb ∪ Fc ∪ Fd, fun R₁ hle hF X₁ f₁ π₁ j hp₁ hj₁ hjf ↦ ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hFa₁, hFb₁⟩, hFc₁⟩, hFd₁⟩ := hF
  have h₂₁ : R₂ ≤ R₁ := Subring.closure_le.mpr
    (Set.union_subset (Set.union_subset (fun x hx ↦ hle hx) hFa₁) hFb₁)
  obtain ⟨m, hmf, hms, hm⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) hp₁
  obtain ⟨n, hnf, hns, hn⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) (IsPullback.of_hasPullback q (spMap (Subring.inclusion hle)))
  have hmc : m ≫ α₂ ≫ β₂ = m := (hc R₁ h₂₁ hFc₁ X₁ f₁ m hm).trans (Category.comp_id _)
  have hnd : n ≫ β₂ ≫ α₂ = n := (hd R₁ h₂₁ hFd₁ _ _ n hn).trans (Category.comp_id _)
  have hjm : j ≫ m = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hj₁, hj₂f]
    · rw [Category.assoc, hms, reassoc_of% hjf, spMap_subtype_comp, hj₂s]
  have hw : (m ≫ ψ₂) ≫ q = f₁ ≫ spMap (Subring.inclusion hle) := by
    rw [Category.assoc, hψ₂q, reassoc_of% hmf, hp₁.w]
  let α : X₁ ⟶ pullback q (spMap (Subring.inclusion hle)) := pullback.lift (m ≫ ψ₂) f₁ hw
  let β : pullback q (spMap (Subring.inclusion hle)) ⟶ X₁ :=
    hp₁.lift (n ≫ χ₂) (pullback.snd _ _) (by rw [Category.assoc, hχ₂q, reassoc_of% hnf,
      pullback.condition])
  have hαf : α ≫ pullback.fst _ _ = m ≫ ψ₂ := pullback.lift_fst _ _ _
  have hαs : α ≫ pullback.snd _ _ = f₁ := pullback.lift_snd _ _ _
  have hβf : β ≫ π₁ = n ≫ χ₂ := hp₁.lift_fst _ _ _
  have hβs : β ≫ f₁ = pullback.snd _ _ := hp₁.lift_snd _ _ _
  have hαn : α ≫ n = m ≫ α₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hnf, hαf, Category.assoc, hα₂f]
    · rw [Category.assoc, hns, reassoc_of% hαs, Category.assoc, hα₂s, hms]
  have hβm : β ≫ m = n ≫ β₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hβf, Category.assoc, hβ₂f]
    · rw [Category.assoc, hms, reassoc_of% hβs, Category.assoc, hβ₂s, hns]
  have h₁ : α ≫ β = 𝟙 X₁ := by
    apply hp₁.hom_ext
    · rw [Category.assoc, hβf, reassoc_of% hαn, Category.id_comp, ← hβ₂f, ← Category.assoc m,
        ← Category.assoc, Category.assoc m, hmc, hmf]
    · rw [Category.assoc, hβs, hαs, Category.id_comp]
  have h₂ : β ≫ α = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hαf, reassoc_of% hβm, Category.id_comp, ← hα₂f, ← Category.assoc n,
        ← Category.assoc, Category.assoc n, hnd, hnf]
    · rw [Category.assoc, hαs, hβs, Category.id_comp]
  exact ⟨m ≫ ψ₂, by rw [reassoc_of% hjm, hψ₂],
    IsPullback.of_iso_pullback ⟨hw⟩ ⟨α, β, h₁, h₂⟩ hαf hαs⟩

end GlobalTheory
