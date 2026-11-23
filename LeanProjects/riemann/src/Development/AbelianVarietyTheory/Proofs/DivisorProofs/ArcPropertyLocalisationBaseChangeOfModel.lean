import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels

noncomputable section

namespace GlobalTheory.LocArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}

@[reducible] def arcRestrict (b : O →+* O') (hb : β'.comp b = β) {O'' : Type} [CommRing O''] [IsDomain O'']
    {b' : O' →+* O''} (a : ArcIn D l β' O'' b') : ArcIn D l β O'' (b'.comp b) where
  D₀ := a.D₀
  mod := a.mod
  oa := a.oa
  nontriv := a.nontriv
  even := a.even
  bimult := a.bimult
  gen := a.gen
  w0 := a.w0
  be := a.be
  be_symm := a.be_symm
  be_pos := a.be_pos
  be_adj := a.be_adj
  be_dvd := a.be_dvd
  eta := a.eta
  etaA := a.etaA
  geom := fun F _ _ _ r z hr hz => a.geom F (b r) (b z) (by rw [← hb] at hr; exact hr) (by rw [← hb] at hz; exact hz)

variable (Y : Model Xo c β) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)]

theorem mono_locMap : Mono (locMap Y b).φ :=
  (MorphismProperty.monomorphisms Scheme.{0}).of_isPullback (locMap Y b).cart.1.flip
    (show Mono (pullback.fst Y.s (spMap b)) from inferInstance)

theorem hasArcData_iff {O'' R : Type} [CommRing O''] [IsDomain O''] [CommRing R] [IsDomain R] {b' : O' →+* O''}
    (a : ArcIn D l β' O'' b') (I : Ideal R) (f : O'' →+* R) (u : R) (χ : Sp R ⟶ (locModel Y b hb).X) :
    (locModel Y b hb).HasArcData a I f u χ ↔
      Y.HasArcData (arcRestrict b hb a) I f u (χ ≫ pullback.fst Y.s (spMap b)) := by
  have ej := locModel_j Y b hb
  have em := locModel_m Y b hb
  constructor
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, ej, hy]
      simp only [Category.assoc]
    · have := mono_locMap Y b
      rw [← cancel_mono (locMap Y b).φ]
      rw [hn, ← em] at k₄
      simp only [Category.assoc]
      exact k₄
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_cancel (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← ej, ← Category.assoc, hy]
      simp only [Category.assoc]
    · have := congrArg (· ≫ (locMap Y b).φ) k₄
      simp only [Category.assoc] at this
      rw [hn, ← em]
      exact this

theorem mem_range_j_iff (x : (locModel Y b hb).X) :
    x ∈ Set.range (locModel Y b hb).j ↔ pullback.fst Y.s (spMap b) x ∈ Set.range Y.j := by
  rw [← locModel_j Y b hb]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, (pullback.fst Y.s (spMap b)).isEmbedding.injective ?_⟩
    rw [← hu, Scheme.Hom.comp_apply]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem locModel_arc (h : Y.N4) : (locModel Y b hb).N4 := by
  intro O'' _ _ _ b' ϖ a hO
  obtain ⟨χ₀, hu, hs⟩ := h O'' (b'.comp b) ϖ (arcRestrict b hb a) hO
  obtain ⟨c₁, c₂, c₃, c₄⟩ := (hu χ₀).1 rfl
  have hw : χ₀ ≫ Y.s = (spMap (PowerSeries.C (R := O'')) ≫ spMap b') ≫ spMap b := by
    rw [c₁, spMap_comp', Category.assoc]
  have hχ : pullback.lift χ₀ _ hw ≫ pullback.fst Y.s (spMap b) = χ₀ := pullback.lift_fst _ _ _
  refine ⟨pullback.lift χ₀ _ hw, fun χ' => ⟨?_, ?_⟩, fun hi y' ev d₁ d₂ d₃ d₄ d₅ => ?_⟩
  · rintro rfl
    refine ⟨pullback.lift_snd _ _ _, fun x => ?_, fun x hx => ?_, ?_⟩
    · rw [mem_abLocus_locModel, ← Scheme.Hom.comp_apply, hχ]
      exact c₂ x
    · rw [mem_range_j_iff, ← Scheme.Hom.comp_apply, hχ]
      exact c₃ x hx
    · rw [hasArcData_iff, hχ]
      exact c₄
  · rintro ⟨d₁, d₂, d₃, d₄⟩
    rw [← cancel_mono (pullback.fst Y.s (spMap b)), hχ]
    refine (hu _).2 ⟨?_, fun x => ?_, fun x hx => ?_, (hasArcData_iff Y b hb a _ _ _ _).1 d₄⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp', ← Category.assoc]
      exact congrArg (· ≫ spMap b) d₁
    · rw [Scheme.Hom.comp_apply, ← mem_abLocus_locModel Y b hb]
      exact d₂ x
    · rw [Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₃ x hx
  · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, hχ]
    refine hs hi _ ev ?_ ?_ ((hasArcData_iff Y b hb a _ _ _ _).1 d₃) d₄ d₅
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp']
      exact congrArg (· ≫ spMap b) d₁
    · rintro _ ⟨q, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₂ ⟨q, rfl⟩

end GlobalTheory.LocArc

theorem GlobalTheory.LocArc.arc_localise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.N4 → (locModel Y b hb).N4 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ b hb _ _ h => GlobalTheory.LocArc.locModel_arc Y b hb h
