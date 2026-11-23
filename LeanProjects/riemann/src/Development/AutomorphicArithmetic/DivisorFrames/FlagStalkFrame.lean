import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

theorem UpperTheory.flag_stalk_frame :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Φ : FlagCpt T e) (y₀ : Φ.Y.X) (R : Type) [CommRing R] (ρ : Φ.Y.X.presheaf.stalk y₀ →+* R) (y : Sp R ⟶ Xo.XF c) (f : c.F →+* R), y ≫ T.jQ = spMap ρ ≫ stalkPt Φ.Y y₀ ≫ Φ.π → y ≫ pullback.snd _ _ = spMap f → LocM.IsFrame T.t f (y ≫ T.j) (Vecs.bc ρ (GlobalTheory.LineNorm.fr Φ y₀).v) := by
  intro E _ _ _ H Dw l Xo c O _ β T F _ _ e Φ y₀ R _ ρ y f hy hf
  have inj : ∀ {A B : Type} [CommRing A] [CommRing B] {a b : A →+* B}, spMap a = spMap b → a = b := fun h =>
    congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) h)
  have cmp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C),
      spMap (b.comp a) = spMap b ≫ spMap a := fun a b => by rw [← Spec.map_comp]; rfl
  let φ : c.F →+* Φ.Y.X.presheaf.stalk y₀ := (Spec.preimage (stalkPt Φ.Y y₀ ≫ Φ.π ≫ genStr T)).hom
  have hφ : stalkPt Φ.Y y₀ ≫ Φ.π ≫ genStr T = spMap φ := (Spec.map_preimage _).symm
  let a : Φ.Y.X.presheaf.stalk y₀ →+* Φ.Y.Fn := algebraMap (Φ.Y.X.presheaf.stalk y₀) Φ.Y.X.functionField
  have ha : spMap a ≫ stalkPt Φ.Y y₀ = genericPt Φ.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y₀)
  have ainj : Function.Injective a := IsFractionRing.injective (Φ.Y.X.presheaf.stalk y₀) Φ.Y.X.functionField
  have h : constF e Φ.Y = a.comp φ := inj (by
    have h1 : genericPt Φ.Y ≫ Φ.Y.str = spMap (algebraMap F Φ.Y.Fn) := (GlobalTheory.FlagBundle.ratOf Φ.Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    have h4 : spMap (constF e Φ.Y) = spMap (algebraMap F Φ.Y.Fn) ≫ spMap e.symm.toRingHom := cmp _ _
    rw [cmp, h4, ← hφ, ← h1, ← Φ.π_str, ← ha]
    simp only [Category.assoc, h2, Category.comp_id])
  have h' : constF e Φ.Y = a.comp (Φ.gr_spec y₀).choose := (GlobalTheory.LineNorm.fr_spec Φ y₀).1.2.1
  have hφ₁ : φ = (Φ.gr_spec y₀).choose :=
    RingHom.ext fun x => ainj (RingHom.congr_fun (h.symm.trans h') x)
  have hj : T.jQ ≫ genStr T = pullback.snd _ _ := T.jQ_over
  have hf' : f = ρ.comp (Φ.gr_spec y₀).choose := inj (by
    rw [cmp, ← hf, ← hj, ← hφ₁, ← hφ, reassoc_of% hy])
  have hx : y ≫ T.j = spMap ρ ≫ stalkPt Φ.Y y₀ ≫ Φ.π ≫ genι T := by
    have : T.j = T.jQ ≫ genι T := rfl
    rw [this, reassoc_of% hy]
  rw [hf', hx]
  exact GlobalTheory.LineNorm.isFrame_fr Φ y₀ ρ
