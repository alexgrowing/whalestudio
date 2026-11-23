import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace CosieveSiteLaws

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}}

abbrev ptZ (q : Z ⟶ Spec (CommRingCat.of K)) (T : Thick (smFun Z q)) : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ Z :=
  pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T

theorem pt_hom (q : Z ⟶ Spec (CommRingCat.of K)) {T T' : Thick (smFun Z q)} (f : T ⟶ T') :
    ptZ q T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) ≫ ptZ q T := by
  have h := congrArg (fun z : (smFun Z q).Pt.obj (CommRingCat.of (T'.B ⧸ T'.J)) =>
    (show PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T'.B ⧸ T'.J) from z).1.2) f.pt
  exact h.symm

theorem inU_iff (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) (T : Thick (smFun Z q)) :
    inU q V T ↔ ⊤ ≤ ptZ q T ⁻¹ᵁ V := Iff.rfl

theorem inU_cosieve (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) : Cosieve (inU q V) := by
  intro T T' f hT
  rw [inU_iff] at hT ⊢
  rw [pt_hom q f, Scheme.Hom.comp_preimage]
  rw [top_le_iff] at hT ⊢
  rw [hT, Scheme.Hom.preimage_top]

theorem on_cosieve (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) : Cosieve (On q i) := by
  rintro T T' f ⟨w, hw⟩
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) ≫ w, ?_⟩
  change _ = ptZ q T'
  rw [pt_hom q f, Category.assoc]
  exact congrArg _ hw

theorem inU_top (q : Z ⟶ Spec (CommRingCat.of K)) (T : Thick (smFun Z q)) : inU q ⊤ T := by
  rw [inU_iff, Scheme.Hom.preimage_top]

theorem inU_inf (q : Z ⟶ Spec (CommRingCat.of K)) (V V' : Z.Opens) (T : Thick (smFun Z q)) :
    inU q (V ⊓ V') T ↔ inU q V T ∧ inU q V' T := by
  rw [inU_iff, inU_iff, inU_iff, Scheme.Hom.preimage_inf, le_inf_iff]

theorem pt_G (q : Z ⟶ Spec (CommRingCat.of K)) (u : Y ⟶ Z) (T : Thick (smFun Y (u ≫ q))) :
    ptZ q ((smS u rfl).G.obj T) = ptZ (u ≫ q) T ≫ u := rfl

theorem inU_pull (q : Z ⟶ Spec (CommRingCat.of K)) (u : Y ⟶ Z) (V : Z.Opens) (T : Thick (smFun Y (u ≫ q))) :
    inU (u ≫ q) (u ⁻¹ᵁ V) T ↔ inU q V ((smS u rfl).G.obj T) := by
  rw [inU_iff, inU_iff, pt_G, Scheme.Hom.comp_preimage]

theorem on_pull (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (u : Y ⟶ Z) (T : Thick (smFun Y (u ≫ q))) :
    On (u ≫ q) (pullback.snd i u) T ↔ On q i ((smS u rfl).G.obj T) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ pullback.fst i u, ?_⟩
    change _ = ptZ q ((smS u rfl).G.obj T)
    rw [pt_G, Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ u) hw
  · rintro ⟨w, hw⟩
    have hw' : w ≫ i = ptZ (u ≫ q) T ≫ u := hw.trans (pt_G q u T)
    exact ⟨pullback.lift w (ptZ (u ≫ q) T) hw', pullback.lift_snd _ _ _⟩

end CosieveSiteLaws

open CosieveSiteLaws in
theorem siteLaws_pf : SiteLaws := by
  intro K _ W Z Y q i u
  exact ⟨fun V => inU_cosieve q V, on_cosieve q i, fun T => inU_top q T, fun V V' T => inU_inf q V V' T,
    fun V T => inU_pull q u V T, fun T => on_pull q i u T⟩

end CrystallineSemistableComparison.Onto
