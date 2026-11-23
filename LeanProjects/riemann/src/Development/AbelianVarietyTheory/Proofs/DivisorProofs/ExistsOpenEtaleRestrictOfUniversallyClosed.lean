import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_open_etale_restrict_of_universallyClosed : ∀ (X P' T : Scheme.{0}) (a : X ⟶ P') (W1 : P'.Opens) (c : (a ⁻¹ᵁ W1).toScheme ⟶ T) (x : P'), UniversallyClosed a → x ∈ W1 → (∀ z : (a ⁻¹ᵁ W1).toScheme, ((a ⁻¹ᵁ W1).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)) → ∃ W : P'.Opens, W ≤ W1 ∧ x ∈ W ∧ ∀ hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ W1, Etale (X.homOfLE hle ≫ c) := by
  intro X P' T a W1 c x ha hx hloc
  have hEt : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  let S : Set (a ⁻¹ᵁ W1).toScheme := {z | ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)}
  have hS : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨U, hz, hU⟩
    exact ⟨U, fun y hy => ⟨U, hy, hU⟩, U.isOpen, hz⟩
  let Z : Set X := ((a ⁻¹ᵁ W1).ι '' S)ᶜ
  have hZ : IsClosed Z := ((a ⁻¹ᵁ W1).ι.isOpenEmbedding.isOpenMap _ hS).isClosed_compl
  have haZ : IsClosed (a '' Z) := a.isClosedMap _ hZ
  refine ⟨W1 ⊓ ⟨(a '' Z)ᶜ, haZ.isOpen_compl⟩, inf_le_left, ⟨hx, ?_⟩, ?_⟩
  · rintro ⟨z, hzZ, hzx⟩
    apply hzZ
    have hz1 : z ∈ a ⁻¹ᵁ W1 := by
      show a z ∈ W1
      rw [hzx]; exact hx
    have hι : (a ⁻¹ᵁ W1).ι ⟨z, hz1⟩ = z := Scheme.Opens.ι_apply _ _
    refine ⟨⟨z, hz1⟩, hloc ⟨z, hz1⟩ ?_, hι⟩
    exact (Scheme.Hom.comp_apply _ _ _).trans (by rw [hι]; exact hzx)
  · intro hle
    have hcov : ∀ w : (a ⁻¹ᵁ (W1 ⊓ ⟨(a '' Z)ᶜ, haZ.isOpen_compl⟩)).toScheme,
        ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, X.homOfLE hle w ∈ U ∧ Etale (U.ι ≫ c) := by
      intro w
      have hw : a w.1 ∉ a '' Z := w.2.2
      have hw' : w.1 ∉ Z := fun h => hw ⟨w.1, h, rfl⟩
      simp only [Z, Set.mem_compl_iff, not_not] at hw'
      obtain ⟨s, ⟨U, hsU, hU⟩, hs⟩ := hw'
      refine ⟨U, ?_, hU⟩
      have : X.homOfLE hle w = s :=
        Subtype.ext ((Scheme.homOfLE_apply hle w).trans (hs.symm.trans (Scheme.Opens.ι_apply _ s)))
      rw [this]; exact hsU
    choose U hwU hU using hcov
    refine IsZariskiLocalAtSource.of_iSup_eq_top (fun w => (X.homOfLE hle) ⁻¹ᵁ (U w)) ?_ fun w => ?_
    · rw [eq_top_iff]
      intro w _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨w, hwU w⟩
    · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (X.homOfLE hle) (le_refl ((X.homOfLE hle) ⁻¹ᵁ U w)), Category.assoc]
      haveI : IsOpenImmersion ((X.homOfLE hle).resLE (U w) ((X.homOfLE hle) ⁻¹ᵁ U w) le_rfl) := by
        have h2 : IsOpenImmersion ((X.homOfLE hle).resLE (U w) ((X.homOfLE hle) ⁻¹ᵁ U w) le_rfl ≫ (U w).ι) := by
          rw [Scheme.Hom.resLE_comp_ι]; infer_instance
        exact IsOpenImmersion.of_comp _ (U w).ι
      exact IsZariskiLocalAtSource.comp (hU w) _

end GlobalTheory
