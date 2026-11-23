import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FunDescent

noncomputable def coord : Γ(Spec (CommRingCat.of (Polynomial ℤ)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X

theorem hom_ext {Z : Scheme.{0}} {g h : Z ⟶ Spec (CommRingCat.of (Polynomial ℤ))}
    (e : g.appTop.hom coord = h.appTop.hom coord) : g = h := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext'
  · exact RingHom.ext_int _ _
  · exact e

theorem exists_hom {Z : Scheme.{0}} (f : Γ(Z, ⊤)) :
    ∃ g : Z ⟶ Spec (CommRingCat.of (Polynomial ℤ)), g.appTop.hom coord = f := by
  let φ : CommRingCat.of (Polynomial ℤ) ⟶ Γ(Z, ⊤) :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) f)
  refine ⟨ΓSpec.adjunction.homEquiv Z (Opposite.op _) φ.op, ?_⟩
  have := congrArg (fun ψ => ψ.hom Polynomial.X) (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ)
  refine this.trans ?_
  simp [φ]

theorem comp_appTop_apply {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom a = g.appTop.hom (h.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem appTop_injective {X Y : Scheme.{0}} (π : X ⟶ Y) [Epi π] :
    Function.Injective π.appTop.hom := by
  intro a b hab
  obtain ⟨g, rfl⟩ := exists_hom a
  obtain ⟨h, rfl⟩ := exists_hom b
  rw [← comp_appTop_apply, ← comp_appTop_apply] at hab
  rw [(cancel_epi π).1 (hom_ext hab)]

theorem exists_appTop_eq {X Y : Scheme.{0}} (π : X ⟶ Y) [EffectiveEpi π] (f : Γ(X, ⊤))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X), g₁ ≫ π = g₂ ≫ π →
      g₁.appTop.hom f = g₂.appTop.hom f) :
    ∃ a, π.appTop.hom a = f := by
  obtain ⟨g, rfl⟩ := exists_hom f
  have H : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ g = g₂ ≫ g := by
    intro Z g₁ g₂ e
    apply hom_ext
    rw [comp_appTop_apply, comp_appTop_apply]
    exact hf Z g₁ g₂ e
  refine ⟨(EffectiveEpi.desc π g H).appTop.hom coord, ?_⟩
  rw [← comp_appTop_apply, EffectiveEpi.fac]

noncomputable def res {X : Scheme.{0}} (U : X.Opens) : Γ(X, U) ⟶ Γ(U.toScheme, ⊤) :=
  U.ι.appLE U ⊤ (by simp)

theorem res_bijective {X : Scheme.{0}} (U : X.Opens) : Function.Bijective (res U).hom := by
  have : res U = U.topIso.inv := by
    simp [res, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  rw [this]
  exact U.topIso.symm.commRingCatIsoToRingEquiv.bijective

theorem res_comp_appTop {X Z : Scheme.{0}} (U : X.Opens) (g : Z ⟶ U.toScheme) (k : Z ⟶ X)
    (e : k = g ≫ U.ι) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    res U ≫ g.appTop = k.appLE U ⊤ h := by
  subst e
  rw [res, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _

theorem res_square {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) :
    res U ≫ (π ∣_ U).appTop = π.app U ≫ res (π ⁻¹ᵁ U) := by
  rw [res_comp_appTop U (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ π) (morphismRestrict_ι π U).symm (by simp),
    res, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

theorem res_square_apply {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) :
    (π ∣_ U).appTop.hom ((res U).hom a) = (res (π ⁻¹ᵁ U)).hom ((π.app U).hom a) :=
  congrArg (fun ψ => ψ.hom a) (res_square π U)

theorem app_injective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] (U : Y.Opens) :
    Function.Injective (π.app U).hom := by
  have : Surjective (π ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  have : Epi (π ∣_ U) := Flat.epi_of_flat_of_surjective _
  intro a b hab
  apply (res_bijective U).1
  apply appTop_injective (π ∣_ U)
  rw [res_square_apply, res_square_apply, hab]

theorem isUnit_of_isUnit_app {X Y : Scheme.{0}} (π : X ⟶ Y) [Surjective π] (U : Y.Opens)
    (a : Γ(Y, U)) (ha : IsUnit ((π.app U).hom a)) : IsUnit a := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ U a fun y hy => ?_
  obtain ⟨x, rfl⟩ := π.surjective y
  have h1 : X.basicOpen ((π.app U).hom a) = π ⁻¹ᵁ U := X.basicOpen_of_isUnit ha
  have h2 : x ∈ π ⁻¹ᵁ (Y.basicOpen a) := by
    rw [Scheme.preimage_basicOpen]
    exact h1.ge hy
  exact (Y.mem_basicOpen a (π x) hy).1 h2

theorem exists_app_eq {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π]
    (U : Y.Opens) (f : Γ(X, π ⁻¹ᵁ U))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (π ⁻¹ᵁ U))
      (h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)), g₁ ≫ π = g₂ ≫ π →
      (g₁.appLE _ ⊤ h₁).hom f = (g₂.appLE _ ⊤ h₂).hom f) :
    ∃ a, (π.app U).hom a = f := by
  have : Surjective (π ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  obtain ⟨b, hb⟩ := exists_appTop_eq (π ∣_ U) ((res (π ⁻¹ᵁ U)).hom f) (by
    intro Z g₁ g₂ e
    have k : ∀ g : Z ⟶ (π ⁻¹ᵁ U).toScheme, ⊤ ≤ (g ≫ (π ⁻¹ᵁ U).ι) ⁻¹ᵁ (π ⁻¹ᵁ U) := by
      intro g; simp
    have := hf Z (g₁ ≫ (π ⁻¹ᵁ U).ι) (g₂ ≫ (π ⁻¹ᵁ U).ι) (k _) (k _) (by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% e])
    rw [← res_comp_appTop _ g₁ _ rfl, ← res_comp_appTop _ g₂ _ rfl] at this
    exact this)
  obtain ⟨a, rfl⟩ := (res_bijective U).2 b
  refine ⟨a, (res_bijective _).1 ?_⟩
  rw [← res_square_apply, hb]

end GlobalTheory.FunDescent

namespace GlobalTheory

theorem invariant_functions_descend :
    ∀ (S : Scheme.{0}) (G B T : Over S) [GrpObj G] [GrpObj B] [GrpObj T] (q : G ⟶ B) (i : T ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∀ (U : B.left.Opens), Function.Injective (q.left.app U).hom ∧ (∀ a : Γ(B.left, U), IsUnit ((q.left.app U).hom a) → IsUnit a) ∧ ∀ f : Γ(G.left, q.left ⁻¹ᵁ U), (∀ (Z : Over S) (t : Z ⟶ T) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ U)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ U)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom f = (g.left.appLE _ ⊤ h₂).hom f) → ∃ a : Γ(B.left, U), (q.left.app U).hom a = f := by
  intro S G B T _ _ _ q i hq hi _ _ _ hP U
  refine ⟨FunDescent.app_injective _ U, FunDescent.isUnit_of_isUnit_app _ U, fun f hf => ?_⟩
  refine FunDescent.exists_app_eq q.left U f fun Z g₁ g₂ h₁ h₂ e => ?_
  let Z' : Over S := Over.mk (g₂ ≫ G.hom)
  let k₂ : Z' ⟶ G := Over.homMk g₂ rfl
  let k₁ : Z' ⟶ G := Over.homMk g₁ (by
    change g₁ ≫ G.hom = g₂ ≫ G.hom
    rw [← Over.w q, reassoc_of% e])
  have e' : k₁ ≫ q = k₂ ≫ q := Over.OverMorphism.ext e
  have w : (k₁ * k₂⁻¹) ≫ q = toUnit Z' ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
    rfl
  have ht : (hP.lift _ _ w ≫ i) * k₂ = k₁ := by
    rw [hP.lift_fst, inv_mul_cancel_right]
  have := hf Z' (hP.lift _ _ w) k₂
  rw [ht] at this
  exact this h₁ h₂

end GlobalTheory
