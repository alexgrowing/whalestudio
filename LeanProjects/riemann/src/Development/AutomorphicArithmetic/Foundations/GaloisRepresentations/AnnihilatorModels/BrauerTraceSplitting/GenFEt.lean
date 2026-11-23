import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.HeckeCl

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt gen)

namespace UpperTheory.Gal.crystallineComparison.Br

private theorem range_subset_basicOpen (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) {Y P : Scheme.{0}} (a : P ⟶ Y)
    (c : P ⟶ sp k) : Set.range a ⊆ (Y.basicOpen (l : Γ(Y, ⊤)) : Set Y) := by
  rintro _ ⟨x, rfl⟩
  have h1 : IsUnit ((l : Γ(sp k, ⊤))) := by
    have := (IsUnit.mk0 _ hl).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    simpa using this
  have h2 : IsUnit ((l : Γ(P, ⊤))) := by
    have := h1.map (c.app ⊤).hom
    rwa [map_natCast] at this
  have hu : IsUnit (a.app ⊤ (l : Γ(Y, ⊤))) := by
    rw [map_natCast]
    exact h2
  have hx : x ∈ a ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) := by
    rw [Scheme.preimage_basicOpen, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact hx

theorem genFEt : GenFEt := by
  intro l O k _ _ _ hl Y p T
  have sY := (IsPullback.of_hasPullback p (gen O k)).flip
  have sZ := (IsPullback.of_hasPullback (T.p ≫ p) (gen O k)).flip
  have hsq : IsPullback (pullback.fst (T.p ≫ p) (gen O k)) (bcMap (gen O k) (p := p) T.p rfl)
      T.p (pullback.fst p (gen O k)) := by
    have h := IsPullback.of_right (h₁₁ := bcMap (gen O k) (p := p) T.p rfl)
      (h₁₂ := pullback.snd p (gen O k)) (v₁₁ := pullback.fst (T.p ≫ p) (gen O k))
      (v₁₂ := pullback.fst p (gen O k)) (h₂₁ := T.p) (h₂₂ := p)
      (by rw [bcMap_snd]; exact sZ) (bcMap_fst _ _ _) sY
    exact h.flip
  show FEt (bcMap (gen O k) (p := p) T.p rfl) T.d
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsFinite) hsq T.fin
  · have hr : Set.range (pullback.fst p (gen O k)) ⊆ Set.range (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rw [Scheme.Opens.range_ι]
      exact range_subset_basicOpen l hl _ (pullback.snd p (gen O k))
    let φ := IsOpenImmersion.lift (Y.basicOpen (l : Γ(Y, ⊤))).ι (pullback.fst p (gen O k)) hr
    have hφ : φ ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι = pullback.fst p (gen O k) :=
      IsOpenImmersion.lift_fac _ _ _
    have t := (isPullback_morphismRestrict T.p (Y.basicOpen (l : Γ(Y, ⊤)))).flip
    have w : pullback.fst (T.p ≫ p) (gen O k) ≫ T.p =
        (bcMap (gen O k) (p := p) T.p rfl ≫ φ) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rw [Category.assoc, hφ]
      exact hsq.w
    have sq2 : IsPullback (t.lift _ _ w) (bcMap (gen O k) (p := p) T.p rfl)
        (T.p ∣_ Y.basicOpen (l : Γ(Y, ⊤))) φ := by
      refine IsPullback.of_right (h₁₂ := (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι)
        (h₂₂ := (Y.basicOpen (l : Γ(Y, ⊤))).ι) (v₁₃ := T.p) ?_ (t.lift_snd _ _ w) t
      rw [t.lift_fst, hφ]
      exact hsq
    exact MorphismProperty.of_isPullback (P := @Etale) sq2 T.et
  · intro K _ _ x
    have hlK : (l : K) ≠ 0 := by
      intro h
      apply hl
      apply (Spec.preimage (x ≫ pullback.snd p (gen O k))).hom.injective
      rw [map_natCast, map_zero]
      exact h
    rw [← T.deg K hlK (x ≫ pullback.fst p (gen O k))]
    exact Nat.card_congr
      { toFun := fun y => ⟨y.1 ≫ pullback.fst (T.p ≫ p) (gen O k), by
          rw [Category.assoc, hsq.w, ← Category.assoc, y.2]⟩
        invFun := fun z => ⟨hsq.lift z.1 x z.2, hsq.lift_snd _ _ _⟩
        left_inv := fun y => Subtype.ext (hsq.hom_ext (hsq.lift_fst _ _ _)
          (by rw [hsq.lift_snd]; exact y.2.symm))
        right_inv := fun z => Subtype.ext (hsq.lift_fst _ _ _) }

end UpperTheory.Gal.crystallineComparison.Br
