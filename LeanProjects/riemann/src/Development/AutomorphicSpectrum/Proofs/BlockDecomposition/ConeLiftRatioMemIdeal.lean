import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeUnit

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem pt_of_hom {T T' : Thick (smFun X q)} (φ : T ⟶ T') :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T = pt T' := by
  have := φ.pt
  unfold pt
  rw [← this]
  rfl

theorem spec_comp {C : Type 1} [Category.{0} C] (g : C ⥤ Thick (smFun X q)) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) := by
  have hφ : (g.map (a ≫ b)).φ = (g.map b).φ.comp (g.map a).φ := by rw [g.map_comp]; rfl
  rw [← Spec.map_comp]
  congr 1
  ext x
  show Ideal.Quotient.mk _ ((g.map (a ≫ b)).φ x) = Ideal.Quotient.mk _ ((g.map b).φ ((g.map a).φ x))
  rw [hφ]
  rfl

theorem u_points (D : E.LineData X) {V : Scheme.{0}} {a a' b : V ⟶ D.Y} (ha : a = a')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b ≫ D.f) : D.u a b h = D.u a' b h' := by
  subst ha
  rfl

theorem gamma_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) :=
  congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem r_sub_mem {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D)
    {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) (hc : c = a ≫ b) :
    ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈
      (g.obj c₂).J := by
  subst hc
  have ea := pt_of_hom (g.map a)
  have eb := pt_of_hom (g.map b)
  have ec := pt_of_hom (g.map (a ≫ b))
  have h1 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₁ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ea]
  have h2 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, eb]
  have h3 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ec]
  have wa := Λ.hw a h1
  have wb := Λ.hw b h2
  have wc := Λ.hw (a ≫ b) h3
  have nat := D.nat (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle))) _ _ h1
  have h12 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f := by
    simpa only [Category.assoc] using
      congrArg (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ ·) h1
  have coc := D.coc _ _ _ h12 h2
  have uc := u_points D (show Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ
      (g.map (a ≫ b)).hle)) ≫ Λ.p c₀ = _ by rw [spec_comp, Category.assoc]) h3 (h12.trans h2)
  have A : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) =
      (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c₂).B ⧸ (g.obj c₂).J))).hom.hom
        (D.u _ _ h12).1 := by
    show Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle (Ideal.Quotient.mk (g.obj c₁).J (Λ.w a)) = _
    rw [wa, nat, ← gamma_nat]
    rfl
  have B : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) *
      Ideal.Quotient.mk (g.obj c₂).J (Λ.w b) = Ideal.Quotient.mk (g.obj c₂).J (Λ.w (a ≫ b)) := by
    rw [A, wb, wc, ← map_mul, ← Units.val_mul, coc, uc]
  rw [← Ideal.Quotient.eq, map_one, Units.val_mul, Units.val_mul, map_mul, map_mul, B, ← map_mul, Units.mul_inv, map_one]

theorem r_sub_one : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (σ : ComposableArrows C 2), ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1) ∈ (g.obj (σ.obj (Fin.last 2))).J := by
  intro K _ _ X q C _ g D Λ σ
  exact r_sub_mem Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (by
    rw [← Functor.map_comp]
    rfl)

end GlobalTheory.CompanionTheory.ConeUnit
