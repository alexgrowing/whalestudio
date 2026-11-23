import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

set_option maxHeartbeats 800000 in
theorem isStrictlySemistable_comp_openImmersion {O : Type} [CommRing O] (ϖ : O) {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of O)) (h : GlobalTheory.Et.IsStrictlySemistable ϖ p) (f : Y ⟶ X) [IsOpenImmersion f] :
    GlobalTheory.Et.IsStrictlySemistable ϖ (f ≫ p) := by
  intro y
  obtain ⟨U, hU, hxU, m, r, h1r, hrm, ψ, hψ, hcomp⟩ := h (f.base y)
  obtain ⟨g, hg, hyg⟩ := hU.exists_basicOpen_le (V := f.opensRange) ⟨f.base y, y, rfl⟩ hxU
  haveI := hU.isLocalization_basicOpen g
  haveI : IsIso (f.app (X.basicOpen g)) := f.isIso_app _ hg
  refine ⟨(Opens.map f.base).obj (X.basicOpen g), (hU.basicOpen g).preimage_of_isOpenImmersion f hg, hyg,
    m, r, h1r, hrm,
    (f.app (X.basicOpen g)).hom.comp ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.comp ψ), ?_, ?_⟩
  · have hL : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.Etale :=
      RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway g)
    have h2 := RingHom.Etale.stableUnderComposition _ _ hψ hL
    exact (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom _) (f.app (X.basicOpen g))).mpr h2
  · rw [RingHom.comp_assoc, RingHom.comp_assoc, hcomp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    congr 1
    have key : ∀ e₁ e₂, p.appLE ⊤ U e₁ ≫ X.presheaf.map (homOfLE (X.basicOpen_le g)).op ≫
        f.app (X.basicOpen g) = (f ≫ p).appLE ⊤ ((Opens.map f.base).obj (X.basicOpen g)) e₂ := by
      intro e₁ e₂
      rw [← Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ t) (key _ _)

end CrystallineSemistableComparison
