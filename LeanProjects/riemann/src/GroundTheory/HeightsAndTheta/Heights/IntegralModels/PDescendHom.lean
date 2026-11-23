import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsDescendHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PClearDenominators
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace DescendHom

section General

variable {T Y Z : Scheme.{0}}

lemma hom_app_res {M N : Y.Modules} (χ : M ⟶ N) {U V : Y.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    χ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (χ.app U x) := by
  have h := congrArg (fun f => f.hom x) (χ.mapPresheaf.naturality i.op)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h

lemma res_injective_of_eq (M : Y.Modules) {U V : Y.Opens} (h : U = V) (i : U ⟶ V) :
    Function.Injective (M.presheaf.map i.op) := by
  have : i = eqToHom h := Subsingleton.elim _ _
  subst this
  exact (ConcreteCategory.bijective_of_isIso _).1

lemma pullSectionOn_naturality (g : T ⟶ Y) {M N : Y.Modules} (χ : M ⟶ N) (V : Y.Opens)
    (m : Γ(M, V)) :
    ((Scheme.Modules.pullback g).map χ).app (g ⁻¹ᵁ V) (pullSectionOn g M V m) =
      pullSectionOn g N V (χ.app V m) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality χ
  have h := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ V).hom m) this
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h.symm

lemma pullSectionOn_comp_inv (f : T ⟶ Z) (h : Z ⟶ Y) (M : Y.Modules) (O : Y.Opens) (m : Γ(M, O)) :
    ((Scheme.Modules.pullbackComp f h).inv.app M).app ((f ≫ h) ⁻¹ᵁ O)
      (pullSectionOn (f ≫ h) M O m) =
        pullSectionOn f _ (h ⁻¹ᵁ O) (pullSectionOn h M O m) := by
  have hu := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction h).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ h)) (Scheme.Modules.pullbackComp f h).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hu
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ O).hom m) hu
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, Scheme.Modules.pushforwardComp_hom_app_app] at h'
  exact h'.symm

lemma pullSectionOn_comp_hom (f : T ⟶ Z) (h : Z ⟶ Y) (M : Y.Modules) (O : Y.Opens) (m : Γ(M, O)) :
    ((Scheme.Modules.pullbackComp f h).hom.app M).app ((f ≫ h) ⁻¹ᵁ O)
      (pullSectionOn f _ (h ⁻¹ᵁ O) (pullSectionOn h M O m)) = pullSectionOn (f ≫ h) M O m := by
  rw [← pullSectionOn_comp_inv, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Iso.inv_hom_id_app]
  rfl

lemma pullSectionOn_openImmersion (ι : Z ⟶ Y) [IsOpenImmersion ι] (M : Y.Modules) (O : Y.Opens)
    (m : Γ(M, O)) :
    pullSectionOn ι M O m = ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M).app (ι ⁻¹ᵁ O)
      ((M.restrictAppIso ι (ι ⁻¹ᵁ O)).inv (M.presheaf.map (homOfLE (ι.image_preimage_le O)).op m)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction ι)
    (Scheme.Modules.pullbackPushforwardAdjunction ι) M
  rw [pullSectionOn, ← h]
  rfl

lemma hom_eq_of_pullSectionOn (g : T ⟶ Y) (R : Y.Opens) (hR : g ⁻¹ᵁ R = ⊤) {F G : Y.Modules}
    (χ₁ χ₂ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (h : ∀ V : Y.Opens, V ≤ R → ∀ s : Γ(F, V),
      χ₁.app (g ⁻¹ᵁ V) (pullSectionOn g F V s) = χ₂.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)) :
    χ₁ = χ₂ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  ext V s
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app]
  change χ₁.app (g ⁻¹ᵁ V) (pullSectionOn g F V s) = χ₂.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)
  have hE : g ⁻¹ᵁ (V ⊓ R) = g ⁻¹ᵁ V := le_antisymm ((Opens.map g.base).monotone inf_le_left)
    (fun x hx => ⟨hx, by
      have : x ∈ g ⁻¹ᵁ R := by rw [hR]; trivial
      exact this⟩)
  apply res_injective_of_eq _ hE (homOfLE hE.le)
  rw [← hom_app_res, ← hom_app_res]
  rw [← pullSectionOn_res g F (inf_le_left : V ⊓ R ≤ V) (homOfLE hE.le) s]
  exact h _ inf_le_right _

lemma pullbackHomAlong_rfl (ι : Z ⟶ Y) (g' : T ⟶ Z) {F G : Y.Modules}
    (ψ : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G) :
    pullbackHomAlong (rfl : g' ≫ ι = g' ≫ ι) ψ = (Scheme.Modules.pullbackComp g' ι).inv.app F ≫
      (Scheme.Modules.pullback g').map ψ ≫ (Scheme.Modules.pullbackComp g' ι).hom.app G := by
  simp [pullbackHomAlong, pullbackCompIso, Scheme.Modules.pullbackCongr]

end General

section Descend

variable {T Y Z : Scheme.{0}} (ι : Z ⟶ Y) [IsOpenImmersion ι] (g' : T ⟶ Z) {F G : Y.Modules}
  (φ : (Scheme.Modules.pullback (g' ≫ ι)).obj F ⟶ (Scheme.Modules.pullback (g' ≫ ι)).obj G)
  (hinj : ∀ V : Y.Opens, V ≤ ι.opensRange → Function.Injective (pullSectionOn (g' ≫ ι) G V))
  (t : ∀ V : Y.Opens, V ≤ ι.opensRange → Γ(F, V) → Γ(G, V))
  (ht : ∀ (V : Y.Opens) (hV : V ≤ ι.opensRange) (s : Γ(F, V)),
    pullSectionOn (g' ≫ ι) G V (t V hV s) =
      φ.app ((g' ≫ ι) ⁻¹ᵁ V) (pullSectionOn (g' ≫ ι) F V s))
include hinj ht

lemma t_res {V W : Y.Opens} (hV : V ≤ ι.opensRange) (h : W ≤ V) (s : Γ(F, V)) :
    t W (h.trans hV) (F.presheaf.map (homOfLE h).op s) =
      G.presheaf.map (homOfLE h).op (t V hV s) := by
  apply hinj W (h.trans hV)
  rw [ht, pullSectionOn_res (g' ≫ ι) F h (homOfLE ((Opens.map (g' ≫ ι).base).monotone h)),
    pullSectionOn_res (g' ≫ ι) G h (homOfLE ((Opens.map (g' ≫ ι).base).monotone h)), ht,
    hom_app_res]

lemma t_add {V : Y.Opens} (hV : V ≤ ι.opensRange) (a b : Γ(F, V)) :
    t V hV (a + b) = t V hV a + t V hV b := by
  apply hinj V hV
  rw [map_add, ht, ht, ht, map_add, map_add]

lemma t_zero {V : Y.Opens} (hV : V ≤ ι.opensRange) : t V hV 0 = 0 := by
  apply hinj V hV
  rw [ht, map_zero, map_zero, map_zero]

lemma t_smul {V : Y.Opens} (hV : V ≤ ι.opensRange) (r : Γ(Y, V)) (a : Γ(F, V)) :
    t V hV (r • a) = r • t V hV a := by
  apply hinj V hV
  rw [ht, pullSectionOn_smul, Scheme.Modules.Hom.app_smul, ← ht, pullSectionOn_smul]

def restrictHom : F.restrict ι ⟶ G.restrict ι :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => t (ι ''ᵁ U.unop) (ι.image_le_opensRange _) s
          map_zero' := t_zero ι g' φ hinj t ht _
          map_add' := t_add ι g' φ hinj t ht _ }
      naturality := fun U V i => by
        ext s
        exact t_res ι g' φ hinj t ht (ι.image_le_opensRange _) (ι.image_mono (leOfHom i.unop)) s }
    (fun U r s => t_smul ι g' φ hinj t ht _ ((ι.appIso U.unop).inv r) s)

lemma restrictHom_app (U : Z.Opens) (s : Γ(F, ι ''ᵁ U)) :
    (restrictHom ι g' φ hinj t ht).app U s = t (ι ''ᵁ U) (ι.image_le_opensRange _) s :=
  rfl

def descendPsi : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G :=
  (Scheme.Modules.restrictFunctorIsoPullback ι).inv.app F ≫ restrictHom ι g' φ hinj t ht ≫
    (Scheme.Modules.restrictFunctorIsoPullback ι).hom.app G

lemma descendPsi_pull (V : Y.Opens) (hV : V ≤ ι.opensRange) (s : Γ(F, V)) :
    (descendPsi ι g' φ hinj t ht).app (ι ⁻¹ᵁ V) (pullSectionOn ι F V s) =
      pullSectionOn ι G V (t V hV s) := by
  rw [pullSectionOn_openImmersion ι F, pullSectionOn_openImmersion ι G, descendPsi,
    ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app_assoc,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  congr 1
  exact t_res ι g' φ hinj t ht hV (ι.image_preimage_le V) s

end Descend

end DescendHom

theorem DescendHom.proof : DescendHom.Statement := by
  intro T Y Z ι _ g' g e F G φ hinj hex
  subst e
  choose t ht using hex
  refine ⟨DescendHom.descendPsi ι g' φ hinj t ht, ?_⟩
  have hR : (g' ≫ ι) ⁻¹ᵁ ι.opensRange = ⊤ := top_le_iff.1 fun x _ => ⟨g'.base x, rfl⟩
  refine DescendHom.hom_eq_of_pullSectionOn (g' ≫ ι) ι.opensRange hR _ _ fun V hV s => ?_
  rw [DescendHom.pullbackHomAlong_rfl]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [DescendHom.pullSectionOn_comp_inv]
  erw [DescendHom.pullSectionOn_naturality g' _ (ι ⁻¹ᵁ V), DescendHom.descendPsi_pull ι g' φ hinj t ht V hV s]
  rw [DescendHom.pullSectionOn_comp_hom, ht]

end

end GroundTheory.Heights₂.Heights.Model
