import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueOfDenseOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalSectionOfIsIntegralElemNormalSchemeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenPush

theorem app_injective_of_dense {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (W : Z.Opens) : Function.Injective (j.app W).hom := by
  intro a b hab
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  have h0 : j ⁻¹ᵁ Z.basicOpen (a - b) = ⊥ := by
    rw [Scheme.preimage_basicOpen, map_sub, hab, sub_self, Scheme.basicOpen_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
  obtain ⟨x, hx1, ⟨y, rfl⟩⟩ := hj.inter_open_nonempty _ (Z.basicOpen (a - b)).isOpen ⟨z, hz⟩
  have : y ∈ j ⁻¹ᵁ Z.basicOpen (a - b) := hx1
  rw [h0] at this
  exact this

theorem isIntegral_of_isIso_comp {A B C D : CommRingCat.{0}} (k : A ⟶ B) (f : B ⟶ C) (m : C ⟶ D) [IsIso k]
    [IsIso m] (h : (k ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv k ≫ (k ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv k)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app_of_universallyClosed {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (U : Z₂.Opens) (hU : IsAffineOpen U) : (ρ.app U).hom.IsIntegral := by
  have : IsAffine U.toScheme := hU
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ U)
  rw [morphismRestrict_appTop] at h
  have e : U.ι ''ᵁ ⊤ = U := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (p : A = B), IsIso (eqToHom p) := fun p => by
    subst p; rw [eqToHom_refl]; infer_instance
  refine @isIntegral_of_isIso_comp _ _ _ _ _ _ _ ?_ ?_ h
  · exact hi _
  · exact hi _

theorem exists_app_eq_of_isIntegralElem {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z]
    (j : T ⟶ Z) [IsOpenImmersion j] (hj : Dense (Set.range j)) (U : Z.Opens)
    (s : Γ(T, j ⁻¹ᵁ U)) (hs : (j.app U).hom.IsIntegralElem s) : ∃ h : Γ(Z, U), j.app U h = s :=
  GlobalTheory.T.exists_section_extending_of_dense_openImmersion j hj U s fun u hu => GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme j hj U s hs u hu

theorem app_surjective_of_dense {T Z₁ Z₂ : Scheme.{0}} [IsReduced Z₁] [GlobalTheory.IsNormalScheme Z₂]
    [IsLocallyNoetherian Z₂] (j₁ : T ⟶ Z₁) (j₂ : T ⟶ Z₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h₁ : Dense (Set.range j₁)) (h₂ : Dense (Set.range j₂)) (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (hρ : j₁ ≫ ρ = j₂) (U : Z₂.Opens) (hU : IsAffineOpen U) : Function.Surjective (ρ.app U).hom := by
  subst hρ
  intro t
  have ht : (ρ.app U).hom.IsIntegralElem t := isIntegral_app_of_universallyClosed ρ U hU t
  have hs : ((j₁ ≫ ρ).app U).hom.IsIntegralElem (j₁.app (ρ ⁻¹ᵁ U) t) := by
    change ((j₁.app (ρ ⁻¹ᵁ U)).hom.comp (ρ.app U).hom).IsIntegralElem _
    exact RingHom.IsIntegralElem.map ht _
  obtain ⟨h, hh⟩ := exists_app_eq_of_isIntegralElem (j₁ ≫ ρ) h₂ U _ hs
  refine ⟨h, app_injective_of_dense j₁ h₁ (ρ ⁻¹ᵁ U) ?_⟩
  rw [← hh]
  rfl

section Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isReduced_gen_id (Y : Model Xo c (RingHom.id c.F)) : IsReduced (gen Y) := by
  haveI : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  haveI : IsIso (genι Y) := GlobalTheory.VarFlag.isIso_genι
  exact isReduced_of_isOpenImmersion (genι Y)

theorem comp_genStr (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hρ : Y.jQ ≫ ρ = X.jQ) : ρ ≫ genStr X = genStr Y := by
  haveI := isReduced_gen_id Y
  haveI : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  refine ext_of_isDominant Y.jQ ?_
  rw [← Category.assoc, hρ, X.jQ_over, Y.jQ_over]

theorem isProper_of_jQ (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hρ : Y.jQ ≫ ρ = X.jQ) : IsProper ρ := by
  haveI := isProper_genStr X
  haveI : IsProper (ρ ≫ genStr X) := (comp_genStr X Y ρ hρ) ▸ isProper_genStr Y
  exact IsProper.of_comp ρ (genStr X)

theorem app_surjective (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hρ : Y.jQ ≫ ρ = X.jQ) (U : (gen X).affineOpens) : Function.Surjective (ρ.app U.1).hom := by
  obtain ⟨hN, hL⟩ := GlobalTheory.ModelRelCompare.normal_genericFibre X (GlobalTheory.ModelRelCompare.isDedFrac_in_use c).1
  haveI : GlobalTheory.IsNormalScheme (gen X) := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsLocallyNoetherian (gen X) := hL
  haveI := isReduced_gen_id Y
  haveI := isProper_of_jQ X Y ρ hρ
  haveI := Y.jQ_open
  haveI := X.jQ_open
  exact app_surjective_of_dense Y.jQ X.jQ Y.jQ_dense X.jQ_dense ρ hρ U.1 U.2

end Models

end GlobalTheory.GenPush

theorem GlobalTheory.GenPush.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X), Y.jQ ≫ ρ = X.jQ →
    ∀ U : (gen X).affineOpens, Function.Surjective (ρ.app U.1).hom :=
  fun _ _ _ _ _ _ _ _ _ X Y ρ hρ U => GlobalTheory.GenPush.app_surjective X Y ρ hρ U
