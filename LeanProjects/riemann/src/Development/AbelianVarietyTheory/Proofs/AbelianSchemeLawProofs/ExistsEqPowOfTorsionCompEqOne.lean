import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivisibleHom

variable {S : Scheme.{0}}

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective {X Y Z : Over S} (e : X ⟶ Y) [Flat e.left]
    [Surjective e.left] {f g : Y ⟶ Z} (h : e ≫ f = e ≫ g) : f = g := by
  haveI := Flat.epi_of_flat_of_surjective e.left
  ext1
  rw [← cancel_epi e.left]
  simpa using congrArg CommaMorphism.left h

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.DivisibleHom.exists_lift_point {A A' T : Over S} (m : A' ⟶ A) [Flat m.left]
    [Surjective m.left] (y : T ⟶ A) :
    ∃ (T' : Over S) (e : T' ⟶ T) (x : T' ⟶ A'), Flat e.left ∧ Surjective e.left ∧
      x ≫ m = e ≫ y := by
  refine ⟨Over.mk (pullback.snd m.left y.left ≫ T.hom), Over.homMk (pullback.snd m.left y.left) rfl,
    Over.homMk (pullback.fst m.left y.left) ?_, ?_, ?_, ?_⟩
  · show pullback.fst m.left y.left ≫ A'.hom = pullback.snd m.left y.left ≫ T.hom
    rw [← Over.w m, ← Category.assoc, pullback.condition, Category.assoc, Over.w y]
  · show Flat (pullback.snd m.left y.left)
    infer_instance
  · show Surjective (pullback.snd m.left y.left)
    infer_instance
  · ext1
    simp [pullback.condition]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.DivisibleHom.isMonHom_of_mul_points {G H : Over S} [GrpObj G] [GrpObj H] (e : G ⟶ H)
    (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h
    simpa using h
  have hG : (η : 𝟙_ (Over S) ⟶ G) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hH : (η : 𝟙_ (Over S) ⟶ H) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h := mul (G ⊗ G) (fst G G) (snd G G)
  rw [Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.mul_def] at h
  have ht : lift (fst G G ≫ e) (snd G G ≫ e) = e ⊗ₘ e := by ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [hG, hH, hone]
  · rw [h, ht]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.comp_mulA {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) :
    x ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n = x ^ n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA
  rw [comp_pow, Category.comp_id]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.mulA_comp {A B : Over S} [GrpObj A] [GrpObj B] (u : A ⟶ B) [IsMonHom u]
    (n : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n ≫ u = u ^ n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA
  rw [pow_comp, Category.id_comp]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.DivisibleHom.exists_factor {A B : Over S} [GrpObj A] [IsCommMonObj A]
    [GrpObj B] (M : ℕ)
    [QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (u : A ⟶ B) [IsMonHom u] (hu : ∀ (T : Over S) (x : T ⟶ A), x ^ M = 1 → x ≫ u = 1) :
    ∃ φ : A ⟶ B, _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ = u := by
  have key : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left),
      g₁ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left = g₂ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left → g₁ ≫ u.left = g₂ ≫ u.left := by
    intro Z g₁ g₂ hg
    have hw : g₂ ≫ A.hom = g₁ ≫ A.hom := by
      rw [← Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M), ← Category.assoc, ← hg, Category.assoc]
    let x₁ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₁ rfl
    let x₂ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₂ hw
    have hx : x₁ ^ M = x₂ ^ M := by
      rw [← _root_.GlobalTheory.DivisibleHom.comp_mulA, ← _root_.GlobalTheory.DivisibleHom.comp_mulA]
      ext1
      simpa [x₁, x₂] using hg
    have h1 : (x₁ * x₂⁻¹) ^ M = 1 := by rw [mul_pow, inv_pow, hx, mul_inv_cancel]
    have h3 : IsMonHom.monoidHom u _ (x₁ * x₂⁻¹) = 1 := hu _ _ h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    simpa [x₁, x₂] using congrArg CommaMorphism.left h3
  refine ⟨Over.homMk (EffectiveEpi.desc _ _ key) ?_, ?_⟩
  · rw [← cancel_epi (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left, ← Category.assoc, EffectiveEpi.fac, Over.w u,
      Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M)]
  · ext1
    simp [EffectiveEpi.fac]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.DivisibleHom.isMonHom_of_factor {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
    (M : ℕ) [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (φ : A ⟶ B) [IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ)] : IsMonHom φ := by
  have hmm : ∀ (T : Over S) (a b : T ⟶ A),
      (a * b) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M = (a ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) * (b ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) := by
    intro T a b
    simp only [_root_.GlobalTheory.DivisibleHom.comp_mulA, mul_pow]
  apply _root_.GlobalTheory.DivisibleHom.isMonHom_of_mul_points
  intro T x y
  obtain ⟨T₁, e₁, x', he₁, hs₁, hx'⟩ := _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) x
  haveI := he₁
  haveI := hs₁
  obtain ⟨T₂, e₂, y', he₂, hs₂, hy'⟩ :=
    _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) (e₁ ≫ y)
  haveI := he₂
  haveI := hs₂
  haveI : Flat (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  haveI : Surjective (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  have hxe : (e₂ ≫ e₁) ≫ x = (e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hx', Category.assoc]
  have hye : (e₂ ≫ e₁) ≫ y = y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hy']
  apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (e₂ ≫ e₁)
  calc (e₂ ≫ e₁) ≫ (x * y) ≫ φ = (((e₂ ≫ e₁) ≫ x) * ((e₂ ≫ e₁) ≫ y)) ≫ φ := by
        rw [← Category.assoc (e₂ ≫ e₁), comp_mul]
    _ = (((e₂ ≫ x') * y') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) ≫ φ := by rw [hxe, hye, hmm]
    _ = ((e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) * (y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) := by
        rw [Category.assoc, mul_comp]
    _ = (e₂ ≫ e₁) ≫ ((x ≫ φ) * (y ≫ φ)) := by
        rw [comp_mul, ← Category.assoc (e₂ ≫ e₁) x, ← Category.assoc (e₂ ≫ e₁) y, hxe, hye]
        simp only [Category.assoc]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧ Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
        Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
          (IsUnit (n : Γ(S, ⊤)) → Etale (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left)) →
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (B : Over S) [GrpObj B]
      [IsCommMonObj B] (M : ℕ), 1 ≤ M → ∀ u : P.A ⟶ B, IsMonHom u →
        (∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ u = 1) →
          (∃ φ : P.A ⟶ B, IsMonHom φ ∧ u = φ ^ M) ∧ (u ^ M = 1 → u = 1) := by
  intro H S _ P B _ _ M hM u hu hkill
  obtain ⟨hfin, hflat, hsurj, -⟩ := H S P M hM
  haveI := hfin
  haveI := hflat
  haveI := hsurj
  haveI := hu
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.DivisibleHom.exists_factor M u hkill
  haveI : IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M ≫ φ) := by rw [hφ]; infer_instance
  haveI := _root_.GlobalTheory.DivisibleHom.isMonHom_of_factor M φ
  refine ⟨⟨φ, inferInstance, ?_⟩, fun h => ?_⟩
  · rw [← hφ, _root_.GlobalTheory.DivisibleHom.mulA_comp]
  · apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M)
    rw [_root_.GlobalTheory.DivisibleHom.mulA_comp, h, comp_one]

end GlobalTheory.DivisibleHom
