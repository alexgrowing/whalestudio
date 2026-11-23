import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOverArtinFibreProductIsPushoutStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverTensorIsPullbackOfIsPullbackSquaresStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjOverOfPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GlueGrpLaw

variable {S S' : Scheme.{0}}

theorem left_ext {Y Z : Over S} {W : Scheme.{0}} {u v : W ⟶ (Y ⊗ Z).left}
    (h₁ : u ≫ (fst Y Z).left = v ≫ (fst Y Z).left) (h₂ : u ≫ (snd Y Z).left = v ≫ (snd Y Z).left) : u = v := by
  rw [Over.fst_left] at h₁
  rw [Over.snd_left] at h₂
  exact pullback.hom_ext h₁ h₂

theorem lift_left_fst' {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (fst X Y).left = a.left := by
  rw [← Over.comp_left, lift_fst]

theorem lift_left_snd' {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (snd X Y).left = b.left := by
  rw [← Over.comp_left, lift_snd]

variable {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem one_left (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have : u = 1 := mul_eq_left.1 hu
  rw [← this]
  rfl

theorem unit_compat (h : IsGrpPullback G' G f φ) : f ≫ η[G].left = η[G'].left ≫ φ := by
  have := one_left h (𝟙_ (Over S'))
  simpa [Hom.one_def, Over.toUnit_left] using this

theorem mul_compat (h : IsGrpPullback G' G f φ) (k : (G' ⊗ G').left ⟶ (G ⊗ G).left)
    (hk₁ : k ≫ (fst G G).left = (fst G' G').left ≫ φ) (hk₂ : k ≫ (snd G G).left = (snd G' G').left ≫ φ) :
    k ≫ μ[G].left = μ[G'].left ≫ φ := by
  let x₀ : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((fst G' G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  let y₀ : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((snd G' G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have e := h.2 (G' ⊗ G') (fst G' G') (snd G' G') x₀ y₀ rfl rfl
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at e
  have hl : (lift x₀ y₀).left = k := left_ext (by rw [lift_left_fst', hk₁]; rfl) (by rw [lift_left_snd', hk₂]; rfl)
  rw [← e, hl]

theorem inv_compat (h : IsGrpPullback G' G f φ) : φ ≫ ι[G].left = ι[G'].left ≫ φ := by
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  let u : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk (ι[G'].left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have e := h.2 G' ι[G'] (𝟙 G') u x₀ rfl (by simp [x₀])
  have hι : (ι[G'] : G' ⟶ G') * 𝟙 G' = 1 := by
    rw [show (ι[G'] : G' ⟶ G') = (𝟙 G')⁻¹ by rw [Hom.inv_def, Category.id_comp], inv_mul_cancel]
  rw [hι, ← one_left h G'] at e
  have hu : u * x₀ = 1 := Over.OverMorphism.ext e
  have : u = x₀⁻¹ := eq_inv_of_mul_eq_one_left hu
  have h2 : (x₀ ≫ ι[G]).left = u.left := by rw [← Hom.inv_def, ← this]
  simpa [u, x₀] using h2

end GlobalTheory.GlueGrpLaw

namespace GlobalTheory.GlueGrpLaw

variable {S S' : Scheme.{0}}

section Piece

variable {Y : Over S} {A : Over S'} [GrpObj A] {s : S' ⟶ S} {j : A.left ⟶ Y.left}

noncomputable def push (hj : j ≫ Y.hom = A.hom ≫ s) {T : Over S'} (x : T ⟶ A) : Over.mk (T.hom ≫ s) ⟶ Y :=
  Over.homMk (x.left ≫ j) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [hj, ← Category.assoc, Over.w])

@[simp] theorem push_left (hj : j ≫ Y.hom = A.hom ≫ s) {T : Over S'} (x : T ⟶ A) :
    (push hj x).left = x.left ≫ j := rfl

theorem push_mul (m : Y ⊗ Y ⟶ Y) (hj : j ≫ Y.hom = A.hom ≫ s) (k : (A ⊗ A).left ⟶ (Y ⊗ Y).left)
    (hk₁ : k ≫ (fst Y Y).left = (fst A A).left ≫ j) (hk₂ : k ≫ (snd Y Y).left = (snd A A).left ≫ j)
    (hm : k ≫ m.left = μ[A].left ≫ j) {T : Over S'} (x y : T ⟶ A) :
    lift (push hj x) (push hj y) ≫ m = push hj (x * y) := by
  have hl : (lift (push hj x) (push hj y)).left = (lift x y).left ≫ k := left_ext
    (by rw [lift_left_fst', Category.assoc, hk₁, ← Category.assoc, lift_left_fst', push_left])
    (by rw [lift_left_snd', Category.assoc, hk₂, ← Category.assoc, lift_left_snd', push_left])
  apply Over.OverMorphism.ext
  rw [Over.comp_left, hl, Category.assoc, hm, push_left, Hom.mul_def, Over.comp_left, Category.assoc]

theorem push_inv (n : Y ⟶ Y) (hj : j ≫ Y.hom = A.hom ≫ s) (hn : j ≫ n.left = ι[A].left ≫ j)
    {T : Over S'} (x : T ⟶ A) : push hj x ≫ n = push hj x⁻¹ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, push_left, push_left, Category.assoc, hn, Hom.inv_def, Over.comp_left, Category.assoc]

theorem push_one (e : 𝟙_ (Over S) ⟶ Y) (hj : j ≫ Y.hom = A.hom ≫ s) (he : s ≫ e.left = η[A].left ≫ j)
    {T : Over S'} : toUnit (Over.mk (T.hom ≫ s)) ≫ e = push hj (1 : T ⟶ A) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, push_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
  change (T.hom ≫ s) ≫ e.left = _
  rw [Category.assoc, he, Category.assoc]

theorem push_id_comp (hj : j ≫ Y.hom = A.hom ≫ s) {Z : Over S} (F : Y ⟶ Z) :
    j ≫ F.left = (push hj (𝟙 A) ≫ F).left := by
  rw [Over.comp_left, push_left, Over.id_left, Category.id_comp]

theorem side_one (e : 𝟙_ (Over S) ⟶ Y) (m : Y ⊗ Y ⟶ Y) (hj : j ≫ Y.hom = A.hom ≫ s)
    (k : (A ⊗ A).left ⟶ (Y ⊗ Y).left)
    (hk₁ : k ≫ (fst Y Y).left = (fst A A).left ≫ j) (hk₂ : k ≫ (snd Y Y).left = (snd A A).left ≫ j)
    (he : s ≫ e.left = η[A].left ≫ j) (hm : k ≫ m.left = μ[A].left ≫ j) :
    j ≫ (lift (toUnit Y ≫ e) (𝟙 Y) ≫ m).left = j ≫ (𝟙 Y : Y ⟶ Y).left := by
  rw [push_id_comp hj, push_id_comp hj]
  congr 1
  rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id, push_one e hj he,
    push_mul m hj k hk₁ hk₂ hm, _root_.one_mul]

theorem side_inv (e : 𝟙_ (Over S) ⟶ Y) (m : Y ⊗ Y ⟶ Y) (n : Y ⟶ Y) (hj : j ≫ Y.hom = A.hom ≫ s)
    (k : (A ⊗ A).left ⟶ (Y ⊗ Y).left)
    (hk₁ : k ≫ (fst Y Y).left = (fst A A).left ≫ j) (hk₂ : k ≫ (snd Y Y).left = (snd A A).left ≫ j)
    (he : s ≫ e.left = η[A].left ≫ j) (hm : k ≫ m.left = μ[A].left ≫ j) (hn : j ≫ n.left = ι[A].left ≫ j) :
    j ≫ (lift n (𝟙 Y) ≫ m).left = j ≫ (toUnit Y ≫ e).left := by
  rw [push_id_comp hj, push_id_comp hj]
  congr 1
  rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id, push_inv n hj hn,
    push_mul m hj k hk₁ hk₂ hm, inv_mul_cancel, push_one e hj he]

noncomputable def pushK (hj : j ≫ Y.hom = A.hom ≫ s) (k : (A ⊗ A).left ⟶ (Y ⊗ Y).left)
    (hkw : k ≫ (Y ⊗ Y).hom = (A ⊗ A).hom ≫ s) : Over.mk ((A ⊗ A).hom ≫ s) ⟶ Y ⊗ Y :=
  Over.homMk k hkw

theorem side_comm [IsCommMonObj A] (m : Y ⊗ Y ⟶ Y) (hj : j ≫ Y.hom = A.hom ≫ s)
    (k : (A ⊗ A).left ⟶ (Y ⊗ Y).left)
    (hk₁ : k ≫ (fst Y Y).left = (fst A A).left ≫ j) (hk₂ : k ≫ (snd Y Y).left = (snd A A).left ≫ j)
    (hkw : k ≫ (Y ⊗ Y).hom = (A ⊗ A).hom ≫ s) (hm : k ≫ m.left = μ[A].left ≫ j) :
    k ≫ (lift (fst Y Y) (snd Y Y) ≫ m).left = k ≫ (lift (snd Y Y) (fst Y Y) ≫ m).left := by
  have e₁ : pushK hj k hkw ≫ fst Y Y = push hj (fst A A) := Over.OverMorphism.ext (by
    rw [Over.comp_left, push_left]; exact hk₁)
  have e₂ : pushK hj k hkw ≫ snd Y Y = push hj (snd A A) := Over.OverMorphism.ext (by
    rw [Over.comp_left, push_left]; exact hk₂)
  have r : ∀ F : Y ⊗ Y ⟶ Y, k ≫ F.left = (pushK hj k hkw ≫ F).left := fun F => rfl
  rw [r, r]
  congr 1
  rw [comp_lift_assoc, comp_lift_assoc, e₁, e₂, push_mul m hj k hk₁ hk₂ hm, push_mul m hj k hk₁ hk₂ hm, _root_.mul_comm]

theorem side_assoc (m : Y ⊗ Y ⟶ Y) (hj : j ≫ Y.hom = A.hom ≫ s)
    (k : (A ⊗ A).left ⟶ (Y ⊗ Y).left)
    (hk₁ : k ≫ (fst Y Y).left = (fst A A).left ≫ j) (hk₂ : k ≫ (snd Y Y).left = (snd A A).left ≫ j)
    (hm : k ≫ m.left = μ[A].left ≫ j) (l : ((A ⊗ A) ⊗ A).left ⟶ ((Y ⊗ Y) ⊗ Y).left)
    (hl₁ : l ≫ (fst (Y ⊗ Y) Y).left = (fst (A ⊗ A) A).left ≫ k) (hl₂ : l ≫ (snd (Y ⊗ Y) Y).left = (snd (A ⊗ A) A).left ≫ j)
    (hlw : l ≫ ((Y ⊗ Y) ⊗ Y).hom = ((A ⊗ A) ⊗ A).hom ≫ s) :
    l ≫ (lift (lift (fst _ _ ≫ fst Y Y) (fst _ _ ≫ snd Y Y) ≫ m) (snd (Y ⊗ Y) Y) ≫ m).left =
      l ≫ (lift (fst _ _ ≫ fst Y Y) (lift (fst _ _ ≫ snd Y Y) (snd (Y ⊗ Y) Y) ≫ m) ≫ m).left := by
  let L : Over.mk (((A ⊗ A) ⊗ A).hom ≫ s) ⟶ (Y ⊗ Y) ⊗ Y := Over.homMk l hlw
  have e₁ : L ≫ fst _ _ ≫ fst Y Y = push hj (fst _ _ ≫ fst A A) := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, push_left, Over.comp_left, ← Category.assoc]
    change (l ≫ (fst (Y ⊗ Y) Y).left) ≫ _ = _
    rw [hl₁, Category.assoc, hk₁, Category.assoc])
  have e₂ : L ≫ fst _ _ ≫ snd Y Y = push hj (fst _ _ ≫ snd A A) := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, push_left, Over.comp_left, ← Category.assoc]
    change (l ≫ (fst (Y ⊗ Y) Y).left) ≫ _ = _
    rw [hl₁, Category.assoc, hk₂, Category.assoc])
  have e₃ : L ≫ snd (Y ⊗ Y) Y = push hj (snd (A ⊗ A) A) := Over.OverMorphism.ext (by
    rw [Over.comp_left, push_left]; exact hl₂)
  have r : ∀ F : (Y ⊗ Y) ⊗ Y ⟶ Y, l ≫ F.left = (L ≫ F).left := fun F => rfl
  rw [r, r]
  congr 1
  simp only [comp_lift_assoc, comp_lift, e₁, e₂, e₃]
  rw [push_mul m hj k hk₁ hk₂ hm, push_mul m hj k hk₁ hk₂ hm, push_mul m hj k hk₁ hk₂ hm,
    push_mul m hj k hk₁ hk₂ hm, _root_.mul_assoc]

end Piece

end GlobalTheory.GlueGrpLaw

namespace GlobalTheory.GlueGrpLaw

theorem exists_glued_grp : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsCommMonObj A₁ → IsCommMonObj A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∀ (Y : Over (Spec P)) (j₁ : A₁.left ⟶ Y.left) (j₂ : A₂.left ⟶ Y.left), IsPullback j₁ A₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ A₂.hom Y.hom (Spec.map f₂) → Flat Y.hom → IsPushout ψ₁ ψ₂ j₁ j₂ → ∃ _ : GrpObj Y, IsCommMonObj Y ∧ IsGrpPullback A₁ Y (Spec.map f₁) j₁ ∧ IsGrpPullback A₂ Y (Spec.map f₂) j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ A₁ _ A₂ _ A₀ _ ψ₁ ψ₂ hc₁ hc₂ hψ₁ hψ₂ Y j₁ j₂ hj₁ hj₂ hfl hY
  have pinch := GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂
  have hw : Spec.map g₁ ≫ Spec.map f₁ = Spec.map g₂ ≫ Spec.map f₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hP.w]

  have Q0 : IsPushout (Spec.map g₁) (Spec.map g₂) (Spec.map f₁) (Spec.map f₂) :=
    pinch (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Spec.map f₁) (Spec.map f₂)
      (Spec.map g₁) (Spec.map g₂) (by dsimp; infer_instance) (IsPullback.id_vert _) (IsPullback.id_vert _)
      (IsPullback.id_vert _) hw (by simp)

  obtain ⟨k₁, hk₁f, hk₁s, hk₁⟩ := GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares (Spec.map f₁) A₁ A₁ Y Y j₁ j₁ hj₁ hj₁
  obtain ⟨k₂, hk₂f, hk₂s, hk₂⟩ := GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares (Spec.map f₂) A₂ A₂ Y Y j₂ j₂ hj₂ hj₂
  obtain ⟨i₁, hi₁f, hi₁s, hi₁⟩ := GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares (Spec.map g₁) A₀ A₀ A₁ A₁ ψ₁ ψ₁ hψ₁.1 hψ₁.1
  obtain ⟨i₂, hi₂f, hi₂s, hi₂⟩ := GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares (Spec.map g₂) A₀ A₀ A₂ A₂ ψ₂ ψ₂ hψ₂.1 hψ₂.1
  have hfl2 : Flat (Y ⊗ Y).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hik : i₁ ≫ k₁ = i₂ ≫ k₂ := left_ext
    (by rw [Category.assoc, Category.assoc, hk₁f, hk₂f, reassoc_of% hi₁f, reassoc_of% hi₂f, hY.w])
    (by rw [Category.assoc, Category.assoc, hk₁s, hk₂s, reassoc_of% hi₁s, reassoc_of% hi₂s, hY.w])
  have Q2 : IsPushout i₁ i₂ k₁ k₂ := pinch (Y ⊗ Y) (A₁ ⊗ A₁) (A₂ ⊗ A₂) (A₀ ⊗ A₀) k₁ k₂ i₁ i₂ hfl2 hk₁ hk₂ hi₁ hik hi₂.w

  obtain ⟨l₁, hl₁f, hl₁s, hl₁⟩ := GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares (Spec.map f₁) (A₁ ⊗ A₁) A₁ (Y ⊗ Y) Y k₁ j₁ hk₁ hj₁
  obtain ⟨l₂, hl₂f, hl₂s, hl₂⟩ := GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares (Spec.map f₂) (A₂ ⊗ A₂) A₂ (Y ⊗ Y) Y k₂ j₂ hk₂ hj₂
  obtain ⟨h₁, hh₁f, hh₁s, hh₁⟩ := GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares (Spec.map g₁) (A₀ ⊗ A₀) A₀ (A₁ ⊗ A₁) A₁ i₁ ψ₁ hi₁ hψ₁.1
  obtain ⟨h₂, hh₂f, hh₂s, hh₂⟩ := GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares (Spec.map g₂) (A₀ ⊗ A₀) A₀ (A₂ ⊗ A₂) A₂ i₂ ψ₂ hi₂ hψ₂.1
  have hfl3 : Flat ((Y ⊗ Y) ⊗ Y).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hhl : h₁ ≫ l₁ = h₂ ≫ l₂ := left_ext
    (by rw [Category.assoc, Category.assoc, hl₁f, hl₂f, reassoc_of% hh₁f, reassoc_of% hh₂f, hik])
    (by rw [Category.assoc, Category.assoc, hl₁s, hl₂s, reassoc_of% hh₁s, reassoc_of% hh₂s, hY.w])
  have Q3 : IsPushout h₁ h₂ l₁ l₂ := pinch ((Y ⊗ Y) ⊗ Y) ((A₁ ⊗ A₁) ⊗ A₁) ((A₂ ⊗ A₂) ⊗ A₂) ((A₀ ⊗ A₀) ⊗ A₀)
    l₁ l₂ h₁ h₂ hfl3 hl₁ hl₂ hh₁ hhl hh₂.w

  have he0 : Spec.map g₁ ≫ (η[A₁].left ≫ j₁ : Spec R₁ ⟶ Y.left) = Spec.map g₂ ≫ (η[A₂].left ≫ j₂ : Spec R₂ ⟶ Y.left) := by
    rw [reassoc_of% (unit_compat hψ₁), reassoc_of% (unit_compat hψ₂), hY.w]
  let e : 𝟙_ (Over (Spec P)) ⟶ Y := Over.homMk (Q0.desc (η[A₁].left ≫ j₁ : Spec R₁ ⟶ Y.left)
      (η[A₂].left ≫ j₂ : Spec R₂ ⟶ Y.left) he0) (by
    refine Q0.hom_ext ?_ ?_
    · rw [Q0.inl_desc_assoc, Category.assoc, hj₁.w, ← Category.assoc, Over.w η[A₁]]
      simp
    · rw [Q0.inr_desc_assoc, Category.assoc, hj₂.w, ← Category.assoc, Over.w η[A₂]]
      simp)
  have he₁ : Spec.map f₁ ≫ e.left = η[A₁].left ≫ j₁ := Q0.inl_desc _ _ _
  have he₂ : Spec.map f₂ ≫ e.left = η[A₂].left ≫ j₂ := Q0.inr_desc _ _ _

  have hm0 : i₁ ≫ μ[A₁].left ≫ j₁ = i₂ ≫ μ[A₂].left ≫ j₂ := by
    rw [reassoc_of% (mul_compat hψ₁ i₁ hi₁f hi₁s), reassoc_of% (mul_compat hψ₂ i₂ hi₂f hi₂s), hY.w]
  let m : Y ⊗ Y ⟶ Y := Over.homMk (Q2.desc (μ[A₁].left ≫ j₁) (μ[A₂].left ≫ j₂) hm0) (by
    refine Q2.hom_ext ?_ ?_
    · rw [Q2.inl_desc_assoc, Category.assoc, hj₁.w, ← Category.assoc, Over.w μ[A₁], hk₁.w]
    · rw [Q2.inr_desc_assoc, Category.assoc, hj₂.w, ← Category.assoc, Over.w μ[A₂], hk₂.w])
  have hm₁ : k₁ ≫ m.left = μ[A₁].left ≫ j₁ := Q2.inl_desc _ _ _
  have hm₂ : k₂ ≫ m.left = μ[A₂].left ≫ j₂ := Q2.inr_desc _ _ _

  have hn0 : ψ₁ ≫ ι[A₁].left ≫ j₁ = ψ₂ ≫ ι[A₂].left ≫ j₂ := by
    rw [reassoc_of% (inv_compat hψ₁), reassoc_of% (inv_compat hψ₂), hY.w]
  let n : Y ⟶ Y := Over.homMk (hY.desc (ι[A₁].left ≫ j₁) (ι[A₂].left ≫ j₂) hn0) (by
    refine hY.hom_ext ?_ ?_
    · rw [hY.inl_desc_assoc, Category.assoc, hj₁.w, ← Category.assoc, Over.w ι[A₁]]
    · rw [hY.inr_desc_assoc, Category.assoc, hj₂.w, ← Category.assoc, Over.w ι[A₂]])
  have hn₁ : j₁ ≫ n.left = ι[A₁].left ≫ j₁ := hY.inl_desc _ _ _
  have hn₂ : j₂ ≫ n.left = ι[A₂].left ≫ j₂ := hY.inr_desc _ _ _

  have V1 : lift (toUnit Y ≫ e) (𝟙 Y) ≫ m = 𝟙 Y := Over.OverMorphism.ext (hY.hom_ext
    (side_one e m hj₁.w k₁ hk₁f hk₁s he₁ hm₁) (side_one e m hj₂.w k₂ hk₂f hk₂s he₂ hm₂))
  have V2 : lift n (𝟙 Y) ≫ m = toUnit Y ≫ e := Over.OverMorphism.ext (hY.hom_ext
    (side_inv e m n hj₁.w k₁ hk₁f hk₁s he₁ hm₁ hn₁) (side_inv e m n hj₂.w k₂ hk₂f hk₂s he₂ hm₂ hn₂))
  have V3 : lift (fst Y Y) (snd Y Y) ≫ m = lift (snd Y Y) (fst Y Y) ≫ m := Over.OverMorphism.ext (Q2.hom_ext
    (side_comm m hj₁.w k₁ hk₁f hk₁s hk₁.w hm₁) (side_comm m hj₂.w k₂ hk₂f hk₂s hk₂.w hm₂))
  have V4 : lift (lift (fst _ _ ≫ fst Y Y) (fst _ _ ≫ snd Y Y) ≫ m) (snd (Y ⊗ Y) Y) ≫ m =
      lift (fst _ _ ≫ fst Y Y) (lift (fst _ _ ≫ snd Y Y) (snd (Y ⊗ Y) Y) ≫ m) ≫ m := Over.OverMorphism.ext (Q3.hom_ext
    (side_assoc m hj₁.w k₁ hk₁f hk₁s hm₁ l₁ hl₁f hl₁s hl₁.w) (side_assoc m hj₂.w k₂ hk₂f hk₂s hm₂ l₂ hl₂f hl₂s hl₂.w))
  obtain ⟨G, hGe, hGm, hGn, hGc⟩ := GlobalTheory.exists_grpObj_over_of_points (Spec P) Y e m n
    (fun T x => by
      have := congrArg (x ≫ ·) V1
      simpa [comp_lift_assoc] using this)
    (fun T x => by
      have := congrArg (x ≫ ·) V2
      simpa [comp_lift_assoc] using this)
    (fun T x y => by
      have := congrArg (lift x y ≫ ·) V3
      simpa [comp_lift_assoc] using this)
    (fun T x y z => by
      have := congrArg (lift (lift x y) z ≫ ·) V4
      simpa [comp_lift_assoc] using this)
  refine ⟨G, hGc, ⟨hj₁, fun T x y x₀ y₀ hx hy => ?_⟩, ⟨hj₂, fun T x y x₀ y₀ hx hy => ?_⟩⟩
  · have ex : x₀ = push hj₁.w x := Over.OverMorphism.ext hx
    have ey : y₀ = push hj₁.w y := Over.OverMorphism.ext hy
    rw [ex, ey, Hom.mul_def, hGm, push_mul m hj₁.w k₁ hk₁f hk₁s hm₁, push_left]
  · have ex : x₀ = push hj₂.w x := Over.OverMorphism.ext hx
    have ey : y₀ = push hj₂.w y := Over.OverMorphism.ext hy
    rw [ex, ey, Hom.mul_def, hGm, push_mul m hj₂.w k₂ hk₂f hk₂s hm₂, push_left]

end GlobalTheory.GlueGrpLaw
