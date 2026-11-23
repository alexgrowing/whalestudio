import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift.ProdFil

variable {R : Type} [CommRing R] {I : Ideal R}

theorem left_ext {B : Scheme.{0}} {X Y : Over B} {T : Scheme.{0}} (g h : T ⟶ (X ⊗ Y).left)
    (h1 : g ≫ (fst X Y).left = h ≫ (fst X Y).left) (h2 : g ≫ (snd X Y).left = h ≫ (snd X Y).left) :
    g = h := by
  have w : h ≫ (X ⊗ Y).hom = g ≫ (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y), ← Category.assoc, ← Category.assoc, h1]
  have := CartesianMonoidalCategory.hom_ext (Over.homMk g rfl : Over.mk (g ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y)
    (Over.homMk h w) (Over.OverMorphism.ext (by simpa using h1)) (Over.OverMorphism.ext (by simpa using h2))
  exact congrArg (fun f => f.left) this

theorem primitive_pullback_mem_hodgeFiltration_of_monHom (κ : DividedPowers I) {S : Scheme.{0}} {t : S ⟶ Sp R} {A A' : Over S} [GrpObj A]
    [GrpObj A'] (f : A' ⟶ A) [IsMonHom f] {X X' : Over (Sp R)} {i : A.left ⟶ X.left} {i' : A'.left ⟶ X'.left}
    (w : i ≫ X.hom = A.hom ≫ t) (w' : i' ≫ X'.hom = A'.hom ≫ t) (m : X'.left ⟶ X.left) (hm : m ≫ X.hom = X'.hom)
    (e : f.left ≫ i = i' ≫ m) {c : prim κ t A} (hc : c ∈ primitiveCrystalHodgeLiftClasses κ A X i w) :
    primPull κ t f c ∈ primitiveCrystalHodgeLiftClasses κ A' X' i' w' := by
  obtain ⟨a, ha, hac⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hc)
  have hmor : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (X'.hom ≫ 𝟙 _) (RingHom.id R) m :=
    IsMor.of_over (dp0 R) (by rw [← Category.assoc, hm])
  refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨hmor.pull1 a, hmor.pullback1_mem_hodgeFiltration ha, ?_⟩)
  have hfi : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (A'.hom ≫ t) (RingHom.id R) (f.left ≫ i) :=
    IsMor.of_dividedPowersZeroIdeal κ (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, Category.assoc, w,
      ← Category.assoc, Over.w f])
  rw [IsMor.pullback1_comp _ _ hfi (fun _ ↦ rfl) e.symm]
  change _ = (homMor κ t f).isMor.pull1 c.1
  rw [show (c : Cris.H1 κ (A.hom ≫ t)) = _ from hac.symm]
  exact (IsMor.pullback1_comp _ _ hfi (fun _ ↦ rfl) rfl a).symm

theorem schemeFil_tensor_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left)
    (wi : i ≫ X.hom = A₀.hom ≫ spMap π) (wj : j ≫ Y.hom = B₀.hom ≫ spMap π)
    (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (wl : l ≫ (X ⊗ Y).hom = (A₀ ⊗ B₀).hom ≫ spMap π) (d : Crys κ (spMap π) (A₀ ⊗ B₀)),
    d ∈ schemeFil κ (A₀ ⊗ B₀) (X ⊗ Y) l wl ↔
      push κ (spMap π) (fst A₀ B₀) d ∈ schemeFil κ A₀ X i wi ∧ push κ (spMap π) (snd A₀ B₀) d ∈ schemeFil κ B₀ Y j wj := by
  intro R R₀ _ _ I κ π A₀ B₀ _ _ X Y i j wi wj e e' he he' h1 h1' l hl1 hl2 wl d
  have hAB : IsMonHom (1 : A₀ ⟶ B₀) := inferInstanceAs (IsMonHom (toUnit A₀ ≫ η[B₀]))
  have hBA : IsMonHom (1 : B₀ ⟶ A₀) := inferInstanceAs (IsMonHom (toUnit B₀ ≫ η[A₀]))
  have one_left : ∀ (C D : Over (Sp R₀)) [GrpObj C] [GrpObj D],
      (1 : C ⟶ D).left = C.hom ≫ (1 : Over.mk (𝟙 (Sp R₀)) ⟶ D).left := by
    intro C D _ _
    have : (1 : C ⟶ D) = (Over.homMk C.hom (by simp) : C ⟶ Over.mk (𝟙 (Sp R₀))) ≫ 1 := by simp
    rw [this]; rfl
  constructor
  · intro H
    constructor
    · refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
      rw [push_apply]
      exact (Submodule.mem_dualAnnihilator _).1 H _
        (primitive_pullback_mem_hodgeFiltration_of_monHom κ (fst A₀ B₀) wi wl (fst X Y).left (Over.w _) hl1.symm hc)
    · refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
      rw [push_apply]
      exact (Submodule.mem_dualAnnihilator _).1 H _
        (primitive_pullback_mem_hodgeFiltration_of_monHom κ (snd A₀ B₀) wj wl (snd X Y).left (Over.w _) hl2.symm hc)
  · rintro ⟨H1, H2⟩
    refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
    let ι₁ : A₀ ⟶ A₀ ⊗ B₀ := lift (𝟙 A₀) 1
    let ι₂ : B₀ ⟶ A₀ ⊗ B₀ := lift 1 (𝟙 B₀)
    have hmul : (fst A₀ B₀ ≫ ι₁) * (snd A₀ B₀ ≫ ι₂) = 𝟙 _ := by
      ext
      · rw [MonObj.mul_comp]; simp [ι₁, ι₂]
      · rw [MonObj.mul_comp]; simp [ι₁, ι₂]
    have hdec : c = primPull κ _ (fst A₀ B₀) (primPull κ _ ι₁ c) + primPull κ _ (snd A₀ B₀) (primPull κ _ ι₂ c) := by
      apply Subtype.ext
      have := c.2 (A₀ ⊗ B₀) (fst A₀ B₀ ≫ ι₁) (snd A₀ B₀ ≫ ι₂)
      rw [hmul, ← pullOver_pullOver, ← pullOver_pullOver] at this
      have hid : pullOver κ (spMap π) (𝟙 (A₀ ⊗ B₀)) (c : Cris.H1 κ ((A₀ ⊗ B₀).hom ≫ spMap π)) = c :=
        IsMor.pullCohomologyOne_id _ _
      rw [← hid, this]; rfl

    let mX : X ⟶ X ⊗ Y := lift (𝟙 X) (Over.homMk (X.hom ≫ e') (by simp [he']))
    let mY : Y ⟶ X ⊗ Y := lift (Over.homMk (Y.hom ≫ e) (by simp [he])) (𝟙 Y)
    have eX : ι₁.left ≫ l = i ≫ mX.left := by
      apply left_ext
      · rw [Category.assoc, hl1, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp [ι₁, mX]
      · rw [Category.assoc, hl2, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp only [ι₁, mX, lift_snd, Over.homMk_left]
        rw [one_left, Category.assoc, h1', ← Category.assoc, ← wi, Category.assoc]
    have eY : ι₂.left ≫ l = j ≫ mY.left := by
      apply left_ext
      · rw [Category.assoc, hl1, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp only [ι₂, mY, lift_fst, Over.homMk_left]
        rw [one_left, Category.assoc, h1, ← Category.assoc, ← wj, Category.assoc]
      · rw [Category.assoc, hl2, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp [ι₂, mY]
    have k1 := primitive_pullback_mem_hodgeFiltration_of_monHom κ ι₁ wl wi mX.left (Over.w _) eX hc
    have k2 := primitive_pullback_mem_hodgeFiltration_of_monHom κ ι₂ wl wj mY.left (Over.w _) eY hc
    rw [hdec, map_add, ← push_apply κ _ (fst A₀ B₀) d, ← push_apply κ _ (snd A₀ B₀) d, (Submodule.mem_dualAnnihilator _).1 H1 _ k1,
      (Submodule.mem_dualAnnihilator _).1 H2 _ k2, add_zero]

end GlobalTheory.SqLift.ProdFil
