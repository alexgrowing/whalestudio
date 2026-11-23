import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PinchLift

theorem exists_gen_away_of_closed : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X'), L'.IsLB → ∀ x : X, (∀ z : Z, i z ≠ x) → ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ), x ∈ W ∧ i ⁻¹ᵁ W = ⊥ ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' := by
  intro X X' Z Z' p i i' p' _ hp hi hG L' hL x hx
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hxU : x ∈ U := by rintro ⟨z, rfl⟩; exact hx z rfl
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  have hiV : ∀ {O : X.Opens}, O ≤ V → i ⁻¹ᵁ O = ⊥ := fun {O} hO =>
    eq_bot_iff.2 fun z hz => (hVU (hO hz) ⟨z, rfl⟩).elim
  have hbot : i ⁻¹ᵁ V = ⊥ := hiV le_rfl
  have hsZ : Subsingleton Γ(Z, i ⁻¹ᵁ V) := by rw [hbot]; infer_instance
  have hbot' : i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V) = ⊥ :=
    eq_bot_iff.2 fun z hz => (hVU (show i (p' z) ∈ V from hz.2) ⟨p' z, rfl⟩).elim
  have hsZ' : Subsingleton Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) := by rw [hbot']; infer_instance
  have hbij : Function.Bijective (p.app V).hom := by
    constructor
    · intro s t hst
      have h1 := hG V ((p.app V).hom s) ((i.app V).hom s) (Subsingleton.elim _ _)
      exact h1.unique ⟨rfl, rfl⟩ ⟨hst.symm, Subsingleton.elim _ _⟩
    · intro a
      obtain ⟨s, hs, -⟩ := hG V a 0 (Subsingleton.elim _ _)
      exact ⟨s, hs.1⟩
  haveI : IsIso (p.app V) := (ConcreteCategory.isIso_iff_bijective (p.app V)).2 hbij
  haveI : IsIso (p ∣_ V) := (isIso_morphismRestrict_iff_isIso_app p hV).2 inferInstance
  have hg : ∀ y, (p ∣_ V ≫ V.ι) y = p ((p ⁻¹ᵁ V).ι y) := fun y => by rw [morphismRestrict_ι]; rfl
  obtain ⟨y, hy⟩ : ∃ y, (p ∣_ V ≫ V.ι) y = x := by
    obtain ⟨v, hv⟩ := (p ∣_ V).surjective ⟨x, hxV⟩
    exact ⟨v, by show V.ι ((p ∣_ V) v) = x; rw [hv]; rfl⟩
  obtain ⟨k₀, hk₀⟩ := exists_chart hL ((p ⁻¹ᵁ V).ι y)
  let W : X.Opens := (p ∣_ V ≫ V.ι) ''ᵁ ((p ⁻¹ᵁ V).ι ⁻¹ᵁ L'.U k₀)
  have hmemW : ∀ z, z ∈ W ↔ ∃ w, (p ⁻¹ᵁ V).ι w ∈ L'.U k₀ ∧ (p ∣_ V ≫ V.ι) w = z := fun z => Iff.rfl
  have hxW : x ∈ W := (hmemW x).2 ⟨y, hk₀, hy⟩
  have hWV : W ≤ V := by
    intro z hz
    obtain ⟨w, -, rfl⟩ := (hmemW z).1 hz
    rw [hg]; exact w.2
  have hWk : p ⁻¹ᵁ W ≤ L'.U k₀ := by
    intro x'' hx''
    obtain ⟨w, hw, hwe⟩ := (hmemW _).1 hx''
    have hv : x'' ∈ p ⁻¹ᵁ V := hWV hx''
    have : (⟨x'', hv⟩ : (p ⁻¹ᵁ V).toScheme) = w :=
      (p ∣_ V ≫ V.ι).isOpenEmbedding.injective (by rw [hwe]; exact hg _)
    rw [← this] at hw; exact hw
  refine ⟨W, fun k => res (le_inf inf_le_left (inf_le_right.trans hWk)) (L'.g k k₀), hxW, hiV hWV, ?_⟩
  intro k l z hk hl hz
  have hz0 : z ∈ L'.U k₀ := hWk hz
  rw [gm_res (𝟙 X') z _ (show z ∈ L'.U k ⊓ p ⁻¹ᵁ W from ⟨hk, hz⟩),
    gm_res (𝟙 X') z _ (show z ∈ L'.U l ⊓ p ⁻¹ᵁ W from ⟨hl, hz⟩)]
  exact (gm_cocycle hL (𝟙 X') z hk hl hz0).symm

end GlobalTheory.PinchLift
