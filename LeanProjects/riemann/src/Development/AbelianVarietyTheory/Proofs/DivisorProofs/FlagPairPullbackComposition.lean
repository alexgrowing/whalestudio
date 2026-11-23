import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

namespace GlobalTheory.Vert.PullCoh

def cmp' {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C) (w : A ⟶ C) (h : u ≫ v = w) :
    Scheme.Modules.pullback v ⋙ Scheme.Modules.pullback u ≅ Scheme.Modules.pullback w :=
  Scheme.Modules.pullbackComp u v ≪≫ Scheme.Modules.pullbackCongr h

theorem cmp'_assoc {A B C D : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C) (t : C ⟶ D) (uv : A ⟶ C)
    (vt : B ⟶ D) (uvt : A ⟶ D) (h₁ : u ≫ v = uv) (h₂ : v ≫ t = vt) (h₃ : uv ≫ t = uvt)
    (h₄ : u ≫ vt = uvt) (M : D.Modules) :
    (cmp' u v uv h₁).hom.app ((Scheme.Modules.pullback t).obj M) ≫ (cmp' uv t uvt h₃).hom.app M =
      (Scheme.Modules.pullback u).map ((cmp' v t vt h₂).hom.app M) ≫ (cmp' u vt uvt h₄).hom.app M := by
  subst h₁ h₂ h₃
  have e := congr_app (Scheme.Modules.pseudofunctor_associativity u v t) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at e
  simp only [cmp', Scheme.Modules.pullbackCongr, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app,
    eqToHom_refl, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [← e]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

theorem cmp'_rfl_hom_app {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C) (M : C.Modules) :
    (cmp' u v (u ≫ v) rfl).hom.app M = (Scheme.Modules.pullbackComp u v).hom.app M := by
  simp [cmp', Scheme.Modules.pullbackCongr]

def sqIso {X X₁ G G₁ : Scheme.{0}} (f : X₁ ⟶ X) (ι : G ⟶ X) (ι₁ : G₁ ⟶ X₁) (a : G₁ ⟶ G)
    (h : ι₁ ≫ f = a ≫ ι) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback ι₁ ≅
      Scheme.Modules.pullback ι ⋙ Scheme.Modules.pullback a :=
  Scheme.Modules.pullbackComp _ f ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp _ _).symm

theorem sqIso_hom_app {X X₁ G G₁ : Scheme.{0}} (f : X₁ ⟶ X) (ι : G ⟶ X) (ι₁ : G₁ ⟶ X₁)
    (a : G₁ ⟶ G) (h : ι₁ ≫ f = a ≫ ι) (M : X.Modules) :
    (sqIso f ι ι₁ a h).hom.app M =
      (cmp' ι₁ f (a ≫ ι) h).hom.app M ≫ (cmp' a ι (a ≫ ι) rfl).inv.app M := by
  simp [sqIso, cmp', Scheme.Modules.pullbackCongr]

theorem sqIso_comp {X X₁ X₂ G G₁ G₂ : Scheme.{0}} (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) (ι : G ⟶ X)
    (ι₁ : G₁ ⟶ X₁) (ι₂ : G₂ ⟶ X₂) (a : G₁ ⟶ G) (b : G₂ ⟶ G₁) (c : G₂ ⟶ G)
    (h₁ : ι₁ ≫ f = a ≫ ι) (h₂ : ι₂ ≫ g = b ≫ ι₁) (h₃ : ι₂ ≫ (g ≫ f) = c ≫ ι) (hc : b ≫ a = c)
    (M : X.Modules) :
    (sqIso g ι₁ ι₂ b h₂).hom.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullback b).map ((sqIso f ι ι₁ a h₁).hom.app M) =
      (Scheme.Modules.pullback ι₂).map ((Scheme.Modules.pullbackComp g f).hom.app M) ≫
        (sqIso (g ≫ f) ι ι₂ c h₃).hom.app M ≫
          (cmp' b a c hc).inv.app ((Scheme.Modules.pullback ι).obj M) := by
  have hK : b ≫ (a ≫ ι) = c ≫ ι := by rw [← hc, Category.assoc]
  have hK' : (b ≫ ι₁) ≫ f = c ≫ ι := by rw [Category.assoc, h₁, ← Category.assoc, hc]
  have A₁ := cmp'_assoc ι₂ g f (b ≫ ι₁) (g ≫ f) (c ≫ ι) h₂ rfl hK' h₃ M
  have A₂ := cmp'_assoc b ι₁ f (b ≫ ι₁) (a ≫ ι) (c ≫ ι) rfl h₁ hK' hK M
  have A₃ := cmp'_assoc b a ι c (a ≫ ι) (c ≫ ι) hc rfl rfl hK M
  rw [← cancel_mono ((Scheme.Modules.pullback b).map ((cmp' a ι (a ≫ ι) rfl).hom.app M) ≫
    (cmp' b (a ≫ ι) (c ≫ ι) hK).hom.app M)]
  rw [sqIso_hom_app, sqIso_hom_app, sqIso_hom_app]
  have e₀ : (Scheme.Modules.pullback b).map ((cmp' a ι (a ≫ ι) rfl).inv.app M) ≫
      (Scheme.Modules.pullback b).map ((cmp' a ι (a ≫ ι) rfl).hom.app M) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    exact CategoryTheory.Functor.map_id _ _
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [reassoc_of% e₀, ← A₂, Iso.inv_hom_id_app_assoc, A₁, ← A₃, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id, cmp'_rfl_hom_app]

theorem sqIso_pull_comp {X X₁ X₂ G G₁ G₂ : Scheme.{0}} (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) (ι : G ⟶ X)
    (ι₁ : G₁ ⟶ X₁) (ι₂ : G₂ ⟶ X₂) (a : G₁ ⟶ G) (b : G₂ ⟶ G₁) (c : G₂ ⟶ G)
    (h₁ : ι₁ ≫ f = a ≫ ι) (h₂ : ι₂ ≫ g = b ≫ ι₁) (h₃ : ι₂ ≫ (g ≫ f) = c ≫ ι) (hc : b ≫ a = c)
    {E E' : X.Modules}
    (φ : (Scheme.Modules.pullback ι).obj E ⟶ (Scheme.Modules.pullback ι).obj E') :
    ((sqIso g ι₁ ι₂ b h₂).hom.app ((Scheme.Modules.pullback f).obj E) ≫
        (Scheme.Modules.pullback b).map ((sqIso f ι ι₁ a h₁).hom.app E ≫
          (Scheme.Modules.pullback a).map φ ≫ (sqIso f ι ι₁ a h₁).inv.app E') ≫
        (sqIso g ι₁ ι₂ b h₂).inv.app ((Scheme.Modules.pullback f).obj E')) ≫
      (Scheme.Modules.pullback ι₂).map ((Scheme.Modules.pullbackComp g f).hom.app E') =
    (Scheme.Modules.pullback ι₂).map ((Scheme.Modules.pullbackComp g f).hom.app E) ≫
      (sqIso (g ≫ f) ι ι₂ c h₃).hom.app E ≫ (Scheme.Modules.pullback c).map φ ≫
        (sqIso (g ≫ f) ι ι₂ c h₃).inv.app E' := by
  have K := sqIso_comp f g ι ι₁ ι₂ a b c h₁ h₂ h₃ hc E
  have K' := sqIso_comp f g ι ι₁ ι₂ a b c h₁ h₂ h₃ hc E'
  have T : (Scheme.Modules.pullback b).map ((sqIso f ι ι₁ a h₁).inv.app E') ≫
      (sqIso g ι₁ ι₂ b h₂).inv.app ((Scheme.Modules.pullback f).obj E') ≫
        (Scheme.Modules.pullback ι₂).map ((Scheme.Modules.pullbackComp g f).hom.app E') =
      (cmp' b a c hc).hom.app ((Scheme.Modules.pullback ι).obj E') ≫
        (sqIso (g ≫ f) ι ι₂ c h₃).inv.app E' := by
    rw [← cancel_epi ((sqIso g ι₁ ι₂ b h₂).hom.app ((Scheme.Modules.pullback f).obj E') ≫
      (Scheme.Modules.pullback b).map ((sqIso f ι ι₁ a h₁).hom.app E'))]
    conv_rhs => rw [← Category.assoc, K']
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
    exact (Category.comp_id _).symm
  have nat := (cmp' b a c hc).hom.naturality φ
  simp only [Functor.comp_map] at nat
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% K, T, reassoc_of% nat, Iso.inv_hom_id_app_assoc]

end GlobalTheory.Vert.PullCoh

namespace GlobalTheory.Vert.Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

namespace GenIso

theorem pull_hom_eq {Z Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
    {E E' : Z.X.Modules} (φ : Z.GenIso E E') :
    (φ.pull hf).hom = (PullCoh.sqIso f Z.gen.ι Z₁.gen.ι (genMap hf)
      (f.resLE_comp_ι (preimage_gen hf).ge).symm).hom.app E ≫
        (Scheme.Modules.pullback (genMap hf)).map φ.hom ≫
        (PullCoh.sqIso f Z.gen.ι Z₁.gen.ι (genMap hf)
          (f.resLE_comp_ι (preimage_gen hf).ge).symm).inv.app E' := rfl

theorem genMap_comp' {Z Z₁ Z₂ : Model O} {f : Z₁.X ⟶ Z.X} {g : Z₂.X ⟶ Z₁.X}
    (hf : f ≫ Z.str = Z₁.str) (hg : g ≫ Z₁.str = Z₂.str) (hfg : (g ≫ f) ≫ Z.str = Z₂.str) :
    genMap hfg = genMap hg ≫ genMap hf := by
  have e₁ : genMap hf ≫ Z.gen.ι = Z₁.gen.ι ≫ f := f.resLE_comp_ι _
  have e₂ : genMap hg ≫ Z₁.gen.ι = Z₂.gen.ι ≫ g := g.resLE_comp_ι _
  have e₃ : genMap hfg ≫ Z.gen.ι = Z₂.gen.ι ≫ (g ≫ f) := (g ≫ f).resLE_comp_ι _
  rw [← cancel_mono Z.gen.ι, Category.assoc, e₁, ← Category.assoc, e₂, Category.assoc, e₃]

theorem pull_pull_hom' {Z Z₁ Z₂ : Model O} {f : Z₁.X ⟶ Z.X} {g : Z₂.X ⟶ Z₁.X}
    (hf : f ≫ Z.str = Z₁.str) (hg : g ≫ Z₁.str = Z₂.str) (hfg : (g ≫ f) ≫ Z.str = Z₂.str)
    {E E' : Z.X.Modules} (φ : Z.GenIso E E') :
    ((φ.pull hf).pull hg).hom ≫ Z₂.genRes.map ((Scheme.Modules.pullbackComp g f).hom.app E') =
      Z₂.genRes.map ((Scheme.Modules.pullbackComp g f).hom.app E) ≫ (φ.pull hfg).hom := by
  rw [pull_hom_eq hg, pull_hom_eq hf, pull_hom_eq hfg]
  exact PullCoh.sqIso_pull_comp f g Z.gen.ι Z₁.gen.ι Z₂.gen.ι (genMap hf) (genMap hg) (genMap hfg)
    (f.resLE_comp_ι (preimage_gen hf).ge).symm (g.resLE_comp_ι (preimage_gen hg).ge).symm
    ((g ≫ f).resLE_comp_ι (preimage_gen hfg).ge).symm (genMap_comp' hf hg hfg).symm φ.hom

end GenIso

namespace FlagPair

def transport {Z : Model O} {E₁ E₁' E₂ E₂' : Z.X.Modules} {φ₁ : Z.GenIso E₁ E₁'}
    {φ₂ : Z.GenIso E₂ E₂'} {N : ℕ} (P : FlagPair φ₁ N) (e : E₁ ≅ E₂) (e' : E₁' ≅ E₂')
    (h : φ₁.hom ≫ Z.genRes.map e'.hom = Z.genRes.map e.hom ≫ φ₂.hom) : FlagPair φ₂ N where
  fl := P.fl.ofIso e
  fl' := P.fl'.ofIso e'
  gen := P.gen
  gen_ι i := by
    change (P.gen i).hom ≫ Z.genRes.map (P.fl'.ι i ≫ e'.hom) =
      Z.genRes.map (P.fl.ι i ≫ e.hom) ≫ φ₂.hom
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, reassoc_of% (P.gen_ι i),
      h, Category.assoc]

theorem nonempty_pull_comp (Z Z₁ Z₂ : Model O) (f : Hom Z₁ Z) (g : Hom Z₂ Z₁)
    (E E' : Z.X.Modules) (φ : Z.GenIso E E') (N : ℕ)
    (P : FlagPair ((φ.pull f.comp_str).pull g.comp_str) N) :
    Nonempty (FlagPair (φ.pull (g.comp f).comp_str) N) :=
  ⟨P.transport ((Scheme.Modules.pullbackComp g.f f.f).app E)
    ((Scheme.Modules.pullbackComp g.f f.f).app E')
    (GenIso.pull_pull_hom' f.comp_str g.comp_str (g.comp f).comp_str φ)⟩

end FlagPair

end GlobalTheory.Vert.Model
