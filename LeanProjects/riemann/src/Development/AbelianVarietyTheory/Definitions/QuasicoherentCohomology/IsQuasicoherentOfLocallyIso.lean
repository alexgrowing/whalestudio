import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res le_iSup_inf unitMod homOfLinear isoOfLinear toMod)

namespace GlobalTheory

namespace Twist

variable {X Y : Scheme.{0}}

abbrev resM (F : X.Modules) {U V : X.Opens} (h : V ≤ U) : Γ(F, U) →+ Γ(F, V) :=
  ConcreteCategory.hom (F.presheaf.map (homOfLE h).op)

variable {F G : X.Modules}

@[simp] theorem resM_resM {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(F, U)) :
    resM F h₂ (resM F h₁ s) = resM F (h₂.trans h₁) s :=
  QCoh.res_res F h₁ h₂ s

@[simp] theorem resM_self {U : X.Opens} (h : U ≤ U) (s : Γ(F, U)) : resM F h s = s :=
  QCoh.res_self F h s

@[simp] theorem resM_smul {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (s : Γ(F, U)) :
    resM F h (a • s) = resG X h a • resM F h s :=
  F.map_smul (homOfLE h) a s

theorem app_resM (φ : F ⟶ G) {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)) :
    φ.app V (resM F h s) = resM G h (φ.app U s) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) s

abbrev abSheaf (F : X.Modules) : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩

theorem sec_ext_of_cover {ι : Type*} {V : X.Opens} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) {s t : Γ(F, V)} (h : ∀ k, resM F (hW k) s = resM F (hW k) t) : s = t :=
  (abSheaf F).eq_of_locally_eq' W V (fun k => homOfLE (hW k)) hc s t h

theorem exists_sec_of_cover {ι : Type*} {V : X.Opens} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) (s : ∀ k, Γ(F, W k))
    (h : ∀ k l, resM F (inf_le_left : W k ⊓ W l ≤ W k) (s k) =
      resM F (inf_le_right : W k ⊓ W l ≤ W l) (s l)) :
    ∃ t : Γ(F, V), ∀ k, resM F (hW k) t = s k :=
  ((abSheaf F).existsUnique_gluing' W V (fun k => homOfLE (hW k)) hc s h).exists

theorem bijective_app_of_cover (φ : F ⟶ G) {ι : Type*} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (V : X.Opens) (h : ∀ (k : ι) (W : X.Opens), W ≤ V → W ≤ U k → Function.Bijective (φ.app W)) :
    Function.Bijective (φ.app V) := by
  constructor
  · intro s t e
    refine sec_ext_of_cover (fun k => V ⊓ U k) (fun _ => inf_le_left) (le_iSup_inf hU V)
      fun k => (h k _ inf_le_left inf_le_right).1 ?_
    rw [app_resM, app_resM, e]
  · intro t
    choose s hs using fun k => (h k _ inf_le_left inf_le_right).2
      (resM G (inf_le_left : V ⊓ U k ≤ V) t)
    obtain ⟨r, hr⟩ := exists_sec_of_cover (fun k => V ⊓ U k) (fun _ => inf_le_left)
      (le_iSup_inf hU V) s fun k l =>
        (h k _ (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)).1 (by
          rw [app_resM, app_resM, hs, hs, resM_resM, resM_resM])
    refine ⟨r, sec_ext_of_cover (fun k => V ⊓ U k) (fun _ => inf_le_left) (le_iSup_inf hU V)
      fun k => ?_⟩
    rw [← app_resM, hr, hs]

theorem isIso_of_bijective (φ : F ⟶ G) (h : ∀ V, Function.Bijective (φ.app V)) : IsIso φ :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.2 fun V =>
    (ConcreteCategory.isIso_iff_bijective _).2 (h V)

theorem isIso_of_cover (φ : F ⟶ G) {ι : Type*} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (h : ∀ (k : ι) (W : X.Opens), W ≤ U k → Function.Bijective (φ.app W)) : IsIso φ :=
  isIso_of_bijective φ fun V => bijective_app_of_cover φ hU V fun k W _ hW => h k W hW

theorem bijective_smul_of_isUnit {V : X.Opens} {a : Γ(X, V)} (ha : IsUnit a) :
    Function.Bijective fun s : Γ(F, V) => a • s :=
  ha.smul_bijective

def restrictIsoOfLinear {U : X.Opens}
    (φ : ∀ V : X.Opens, V ≤ U → (Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V)))
    (hφ : ∀ {V W : X.Opens} (hV : V ≤ U) (h : W ≤ V) (s : Γ(F, V)),
      φ W (h.trans hV) (resM F h s) = resM G h (φ V hV s))
    (g : Y ⟶ X) [IsOpenImmersion g] (hg : g.opensRange ≤ U) : F.restrict g ≅ G.restrict g :=
  isoOfLinear (F := F.restrict g) (G := G.restrict g)
    (fun W =>
      { toFun := φ (g ''ᵁ W) ((g.image_le_opensRange W).trans hg)
        invFun := (φ (g ''ᵁ W) ((g.image_le_opensRange W).trans hg)).symm
        map_add' := map_add _
        map_smul' := fun a s =>
          (φ (g ''ᵁ W) ((g.image_le_opensRange W).trans hg)).map_smul ((g.appIso W).inv a) s
        left_inv := LinearEquiv.symm_apply_apply _
        right_inv := LinearEquiv.apply_symm_apply _ })
    fun {V W} h s => hφ _ (g.image_mono h) s

set_option backward.isDefEq.respectTransparency false in

def overIsoOfRestrictIso {U : X.Opens} (e : F.restrict U.ι ≅ G.restrict U.ι) :
    F.over U ≅ G.over U :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app F ≪≫ e ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app G).symm)

set_option backward.isDefEq.respectTransparency false in

def generatorsOver {U V : X.Opens} (h : V ≤ U) (σ : (F.over U).GeneratingSections) :
    (F.over V).GeneratingSections :=
  (σ.map (SheafOfModules.overMap X.ringCatSheaf (homOfLE h))
    (SheafOfModules.overMapUnitIso (homOfLE h)).symm).ofEpi
    ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app F).hom

set_option backward.isDefEq.respectTransparency false in

def generatorsOfLocallyIso {ι : Type} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (e : ∀ (k : ι) (W : X.Opens), W ≤ U k → (F.restrict W.ι ≅ G.restrict W.ι))
    (σ : SheafOfModules.LocalGeneratorsData.{0} F) : SheafOfModules.LocalGeneratorsData.{0} G where
  I := σ.I × ι
  X p := σ.X p.1 ⊓ U p.2
  coversTop := by
    have hc : ⨆ k, σ.X k = ⊤ := (Opens.coversTop_iff _ _).1 σ.coversTop
    rw [Opens.coversTop_iff]
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ x))
    obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hU.ge (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨(k, l), hk, hl⟩
  generators p := (generatorsOver inf_le_left (σ.generators p.1)).ofEpi
    (overIsoOfRestrictIso (e p.2 _ inf_le_right)).hom

set_option backward.isDefEq.respectTransparency false in

theorem isFiniteType_of_locally_iso {ι : Type} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (e : ∀ (k : ι) (W : X.Opens), W ≤ U k → (F.restrict W.ι ≅ G.restrict W.ι))
    [hF : F.IsFiniteType] : G.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := hF.exists_localGeneratorsData
  exact ⟨generatorsOfLocallyIso hU e σ, ⟨fun p => ⟨(hσ.isFiniteType p.1).finite⟩⟩⟩

theorem isQuasicoherent_of_locally_iso {ι : Type} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (e : ∀ k : ι, F.restrict (U k).ι ≅ G.restrict (U k).ι)
    [F.IsQuasicoherent] : G.IsQuasicoherent := by
  refine QCoh.isQuasicoherent_of_restrict G (fun k => (U k).ι) (fun x => ?_) fun k => ?_
  · obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hU.ge (Set.mem_univ x))
    exact ⟨l, by rwa [Scheme.Opens.opensRange_ι]⟩
  · exact (SheafOfModules.isQuasicoherent (U k).toScheme.ringCatSheaf).prop_of_iso (e k)
      (inferInstanceAs (F.restrict (U k).ι).IsQuasicoherent)

section Stalk

variable {U : X.Opens} (φ : ∀ V : X.Opens, V ≤ U → (Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V)))
  (hφ : ∀ {V W : X.Opens} (hV : V ≤ U) (h : W ≤ V) (s : Γ(F, V)),
    φ W (h.trans hV) (resM F h s) = resM G h (φ V hV s)) {x : X} (hx : x ∈ U)

theorem germ_resM {V W : X.Opens} (h : W ≤ V) {x : X} (hx : x ∈ W) (s : Γ(F, V)) :
    F.presheaf.germ W x hx (resM F h s) = F.presheaf.germ V x (h hx) s :=
  F.presheaf.germ_res_apply (homOfLE h) x hx s

def stalkHomOfLinear : F.presheaf.stalk x ⟶ G.presheaf.stalk x :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ F.presheaf)
    { pt := G.presheaf.stalk x
      ι :=
        { app := fun W => F.presheaf.map (homOfLE (inf_le_left : W.unop.1 ⊓ U ≤ W.unop.1)).op ≫
            AddCommGrpCat.ofHom (φ (W.unop.1 ⊓ U) inf_le_right).toLinearMap.toAddMonoidHom ≫
              G.presheaf.germ (W.unop.1 ⊓ U) x ⟨W.unop.2, hx⟩
          naturality := fun W W' f => by
            ext (s : Γ(F, W.unop.1))
            have h : W'.unop.1 ≤ W.unop.1 := leOfHom f.unop
            change G.presheaf.germ (W'.unop.1 ⊓ U) x ⟨W'.unop.2, hx⟩
              (φ _ inf_le_right (resM F inf_le_left (resM F h s))) =
              G.presheaf.germ (W.unop.1 ⊓ U) x ⟨W.unop.2, hx⟩
                (φ _ inf_le_right (resM F inf_le_left s))
            rw [← germ_resM (inf_le_inf_right U h) ⟨W'.unop.2, hx⟩, ← hφ, resM_resM,
              resM_resM] } }

theorem stalkHomOfLinear_germ {V : X.Opens} (hV : V ≤ U) (hxV : x ∈ V) (s : Γ(F, V)) :
    stalkHomOfLinear φ hφ hx (F.presheaf.germ V x hxV s) = G.presheaf.germ V x hxV (φ V hV s) := by
  have e : stalkHomOfLinear φ hφ hx (F.presheaf.germ V x hxV s) =
      G.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩ (φ _ inf_le_right (resM F inf_le_left s)) :=
    ConcreteCategory.congr_hom (Limits.colimit.ι_desc
      (F := (OpenNhds.inclusion x).op ⋙ F.presheaf) _ (op ⟨V, hxV⟩)) s
  rw [e, hφ hV]
  exact germ_resM _ _ _

include hx in

theorem exists_germ_eq_of_mem (t : (F.presheaf.stalk x :)) :
    ∃ (V : X.Opens) (_ : V ≤ U) (hxV : x ∈ V) (s : Γ(F, V)), F.presheaf.germ V x hxV s = t := by
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  exact ⟨V ⊓ U, inf_le_right, ⟨hV, hx⟩, resM F inf_le_left s, germ_resM _ _ _⟩

include hφ in

theorem symm_resM {V W : X.Opens} (hV : V ≤ U) (h : W ≤ V) (s : Γ(G, V)) :
    (φ W (h.trans hV)).symm (resM G h s) = resM F h ((φ V hV).symm s) := by
  rw [LinearEquiv.symm_apply_eq, hφ hV, LinearEquiv.apply_symm_apply]

def stalkEquivOfLinear :
    (F.presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] (G.presheaf.stalk x :) where
  toFun := stalkHomOfLinear φ hφ hx
  invFun := stalkHomOfLinear (fun V hV => (φ V hV).symm) (symm_resM φ hφ) hx
  map_add' := map_add _
  map_smul' r t := by
    obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem hx t
    obtain ⟨W, hxW, a, rfl⟩ := X.presheaf.exists_germ_eq r
    have hxVW : x ∈ V ⊓ W := ⟨hxV, hxW⟩
    rw [RingHom.id_apply, ← germ_resM (inf_le_left : V ⊓ W ≤ V) hxVW,
      ← X.presheaf.germ_res_apply (homOfLE (inf_le_right : V ⊓ W ≤ W)) x hxVW,
      ← QCoh.germ_smul, stalkHomOfLinear_germ φ hφ hx (inf_le_left.trans hV),
      stalkHomOfLinear_germ φ hφ hx (inf_le_left.trans hV), map_smul, QCoh.germ_smul]
  left_inv t := by
    obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem hx t
    rw [stalkHomOfLinear_germ φ hφ hx hV, stalkHomOfLinear_germ _ _ hx hV,
      LinearEquiv.symm_apply_apply]
  right_inv t := by
    obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem hx t
    rw [stalkHomOfLinear_germ _ _ hx hV, stalkHomOfLinear_germ φ hφ hx hV,
      LinearEquiv.apply_symm_apply]

theorem stalkEquivOfLinear_germ {V : X.Opens} (hV : V ≤ U) (hxV : x ∈ V) (s : Γ(F, V)) :
    stalkEquivOfLinear φ hφ hx (F.presheaf.germ V x hxV s) =
      G.presheaf.germ V x hxV (φ V hV s) :=
  stalkHomOfLinear_germ φ hφ hx hV hxV s

end Stalk

section Mate

variable {C D : Type*} [Category C] [Category D] {P : C ⥤ D} {Q : D ⥤ C} (adj : P ⊣ Q)
  (S : C ⥤ C) (T : D ⥤ D) (e : Q ⋙ S ≅ T ⋙ Q)

def mateHom (A : C) : P.obj (S.obj A) ⟶ T.obj (P.obj A) :=
  (adj.homEquiv _ _).symm (S.map (adj.unit.app A) ≫ e.hom.app (P.obj A))

theorem mateHom_naturality {A B : C} (f : A ⟶ B) :
    P.map (S.map f) ≫ mateHom adj S T e B = mateHom adj S T e A ≫ T.map (P.map f) := by
  rw [mateHom, mateHom, ← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm, ← S.map_comp_assoc, Category.assoc]
  congr 1
  have h₁ := adj.unit.naturality f
  have h₂ := e.hom.naturality (P.map f)
  dsimp at h₁ h₂ ⊢
  rw [h₁, S.map_comp_assoc, h₂]

theorem isIso_mateHom [S.IsEquivalence] [T.IsEquivalence] (A : C) : IsIso (mateHom adj S T e A) := by
  have key (B : D) : Function.Bijective
      fun ψ : T.obj (P.obj A) ⟶ T.obj B => mateHom adj S T e A ≫ ψ := by
    have h₁ : Function.Bijective fun χ : P.obj A ⟶ B => T.map χ :=
      (Functor.FullyFaithful.ofFullyFaithful T).map_bijective _ _
    rw [← Function.Bijective.of_comp_iff _ h₁, ← Function.Bijective.of_comp_iff'
      (adj.homEquiv (S.obj A) (T.obj B)).bijective]
    have h₂ : Function.Bijective fun χ : A ⟶ Q.obj B => S.map χ :=
      (Functor.FullyFaithful.ofFullyFaithful S).map_bijective _ _
    have h₃ : Function.Bijective fun χ : S.obj A ⟶ S.obj (Q.obj B) =>
        (χ ≫ e.hom.app B : S.obj A ⟶ Q.obj (T.obj B)) :=
      (Iso.homToEquiv (e.app B)).bijective
    convert (h₃.comp h₂).comp (adj.homEquiv A B).bijective using 1
    ext χ
    have h₄ := e.hom.naturality χ
    dsimp at h₄ ⊢
    rw [Adjunction.homEquiv_naturality_right, mateHom, Equiv.apply_symm_apply, Category.assoc,
      Adjunction.homEquiv_unit, S.map_comp_assoc, h₄]
  refine isIso_of_coyoneda_map_bijective _ fun B => ?_
  let i := T.objObjPreimageIso B
  have h₅ : Function.Bijective fun ψ : T.obj (P.obj A) ⟶ T.obj (T.objPreimage B) => ψ ≫ i.hom :=
    (Iso.homToEquiv i).bijective
  have h₆ : Function.Bijective fun ψ : P.obj (S.obj A) ⟶ T.obj (T.objPreimage B) => ψ ≫ i.hom :=
    (Iso.homToEquiv i).bijective
  rw [← Function.Bijective.of_comp_iff _ h₅]
  convert h₆.comp (key _) using 1
  ext ψ
  simp

end Mate

end Twist

end GlobalTheory
