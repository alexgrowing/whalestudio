import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

set_option linter.unusedSimpArgs false

universe u

variable {T' T Y Z : Scheme.{u}}

lemma pullbackCompIso_trans_right {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k) {E : Z.Modules}
    {F F' : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) (δ : F ≅ F') :
    pullbackCompIso e (γ ≪≫ δ) = pullbackCompIso e γ ≪≫ (Scheme.Modules.pullback g).mapIso δ := by
  ext1
  simp [pullbackCompIso]

lemma pullbackCompIso_eq_refl_trans {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e γ = pullbackCompIso e (Iso.refl _) ≪≫ (Scheme.Modules.pullback g).mapIso γ := by
  rw [← pullbackCompIso_trans_right, Iso.refl_trans]

lemma pullbackCompIso_comp (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k') (e' : g' ≫ h = k')
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e' γ = pullbackCompIso ek (pullbackCompIso e γ) ≪≫
      (Scheme.Modules.pullbackComp t g).app F ≪≫ (Scheme.Modules.pullbackCongr eg).app F := by
  subst eg ek e
  ext1
  have assoc := congr_arg (fun φ => φ.app E)
    (Scheme.Modules.pseudofunctor_associativity t g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at assoc
  have nat := (Scheme.Modules.pullbackComp t g).hom.naturality γ.hom
  simp only [Functor.comp_map] at nat
  simp only [pullbackCompIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc, Category.id_comp, eqToIso.inv, eqToIso.hom, eqToHom_app,
    eqToHom_refl, Category.comp_id, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc]
  simp only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [nat]
  have assoc' : (Scheme.Modules.pullbackComp t (g ≫ h)).inv.app E ≫
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullbackComp g h).inv.app E) ≫
        (Scheme.Modules.pullbackComp t g).hom.app ((Scheme.Modules.pullback h).obj E) =
      eqToHom (by rw [Category.assoc]) ≫ (Scheme.Modules.pullbackComp (t ≫ g) h).inv.app E := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp (t ≫ g) h).hom.app E)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact assoc
  slice_rhs 2 3 => erw [Category.id_comp]
  slice_rhs 1 3 => rw [assoc']
  simp only [Category.assoc]

lemma pullbackComp_trans_congr (t : T' ⟶ T) {g : T ⟶ Y} {g' : T' ⟶ Y} (eg : t ≫ g = g')
    (F : Y.Modules) :
    (Scheme.Modules.pullbackComp t g).app F ≪≫ (Scheme.Modules.pullbackCongr eg).app F =
      (pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F))).symm := by
  subst eg
  ext1
  simp [pullbackCompIso, Scheme.Modules.pullbackCongr]

lemma pullbackCompIso_comp' (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k') (e' : g' ≫ h = k')
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e' γ = pullbackCompIso ek (Iso.refl _) ≪≫
      (Scheme.Modules.pullback t).mapIso (pullbackCompIso e γ) ≪≫
      (pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F))).symm := by
  rw [pullbackCompIso_comp t e eg ek e' γ, pullbackComp_trans_congr,
    pullbackCompIso_eq_refl_trans ek (pullbackCompIso e γ), Iso.trans_assoc]

lemma mapIso_pullbackCompIso_refl (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k')
    (e' : g' ≫ h = k') (E : Z.Modules) :
    (Scheme.Modules.pullback t).mapIso (pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback h).obj E))) =
      (pullbackCompIso ek (Iso.refl _)).symm ≪≫ pullbackCompIso e' (Iso.refl _) ≪≫
        pullbackCompIso eg (Iso.refl _) := by
  rw [pullbackCompIso_comp' t e eg ek e']
  ext1
  simp

lemma pullbackCompIso_refl_naturality (t : T' ⟶ T) {g : T ⟶ Y} {g' : T' ⟶ Y} (eg : t ≫ g = g')
    {F F' : Y.Modules} (δ : F ≅ F') :
    pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F)) ≪≫
        (Scheme.Modules.pullback t).mapIso ((Scheme.Modules.pullback g).mapIso δ) =
      (Scheme.Modules.pullback g').mapIso δ ≪≫ pullbackCompIso eg (Iso.refl _) := by
  rw [← pullbackCompIso_eq_refl_trans]
  subst eg
  ext1
  have nat := (Scheme.Modules.pullbackComp t g).inv.naturality δ.hom
  simp only [Functor.comp_map] at nat
  simp [pullbackCompIso, Scheme.Modules.pullbackCongr, nat]

lemma mapIso_pullbackIsoAlong {W' W O O' : Scheme.{0}} (u : W' ⟶ W) {t : W ⟶ O'} {h : O' ⟶ O}
    {k : W ⟶ O} (ek : t ≫ h = k) {t' : W' ⟶ O'} {k' : W' ⟶ O} (ee : t' ≫ h = k')
    (ut : u ≫ t = t') (uk : u ≫ k = k') {A B : O.Modules}
    (ψ : (Scheme.Modules.pullback h).obj A ≅ (Scheme.Modules.pullback h).obj B) :
    (Scheme.Modules.pullback u).mapIso (pullbackIsoAlong ek ψ) =
      (pullbackCompIso uk (Iso.refl ((Scheme.Modules.pullback k).obj A))).symm ≪≫
        pullbackIsoAlong ee ψ ≪≫ pullbackCompIso uk (Iso.refl _) := by
  have hA := mapIso_pullbackCompIso_refl u ek ut uk ee A
  have hB := mapIso_pullbackCompIso_refl u ek ut uk ee B
  have nat := pullbackCompIso_refl_naturality u ut ψ
  simp only [pullbackIsoAlong, Functor.mapIso_trans, Functor.mapIso_symm, hA, hB]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  congr 2
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, nat]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

def starIso {W U V O' O N : Scheme.{0}} {t : W ⟶ O'} {h : O' ⟶ O} {k : W ⟶ O} (ek : t ≫ h = k)
    {ρ : O ⟶ N} {τ : O ⟶ V} {jU : W ⟶ U} {ρU : U ⟶ N} {jV : W ⟶ V} (e7 : k ≫ ρ = jU ≫ ρU)
    (e8 : k ≫ τ = jV) {E' : N.Modules} {E₀ : V.Modules}
    (ψ : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback ρ).obj E') ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback τ).obj E₀)) :
    (Scheme.Modules.pullback jU).obj ((Scheme.Modules.pullback ρU).obj E') ≅
      (Scheme.Modules.pullback jV).obj E₀ :=
  (pullbackCompIso (rfl : jU ≫ ρU = jU ≫ ρU) (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫
    pullbackCompIso e7 (Iso.refl _) ≪≫ pullbackIsoAlong ek ψ ≪≫
    (pullbackCompIso e8 (Iso.refl ((Scheme.Modules.pullback τ).obj E₀))).symm

theorem glue_compat_chase {X XQ Xp V U W Oa Oam ON : Scheme.{0}}
    {ιV : V ⟶ X} {ιU : U ⟶ X} {ιW : W ⟶ X} {jV : W ⟶ V} {jU : W ⟶ U}
    {bQ : XQ ⟶ X} {bp : Xp ⟶ X} {rQp : XQ ⟶ Xp} {c0 : XQ ⟶ V} {rU : Xp ⟶ U}
    {ρU : U ⟶ ON} {rN : Xp ⟶ ON} {ρa : Oa ⟶ ON} {τa : Oa ⟶ V} {cA : XQ ⟶ Oa}
    {h : Oam ⟶ Oa} {cA' : XQ ⟶ Oam} {t : W ⟶ Oam} {k : W ⟶ Oa} {q : XQ ⟶ W}
    (hV : jV ≫ ιV = ιW) (hU : jU ≫ ιU = ιW) (h0 : c0 ≫ ιV = bQ) (hp : rQp ≫ bp = bQ)
    (hrU : rU ≫ ιU = bp) (h5 : rU ≫ ρU = rN) (e1 : cA ≫ ρa = rQp ≫ rN) (e2 : cA ≫ τa = c0)
    (ee : cA' ≫ h = cA) (ek : t ≫ h = k) (e7 : k ≫ ρa = jU ≫ ρU) (e8 : k ≫ τa = jV)
    (qV : q ≫ jV = c0) (qU : q ≫ jU = rQp ≫ rU) (qt : q ≫ t = cA') (qW : q ≫ ιW = bQ)
    {E : X.Modules} {E₀ : V.Modules} {Ep : Xp.Modules} {E' : ON.Modules}
    (e₀ : (Scheme.Modules.pullback ιV).obj E ≅ E₀)
    (eU : (Scheme.Modules.pullback ιU).obj E ≅ (Scheme.Modules.pullback ρU).obj E')
    (σ : (Scheme.Modules.pullback rN).obj E' ≅ Ep)
    (β : (Scheme.Modules.pullback rQp).obj Ep ≅ (Scheme.Modules.pullback c0).obj E₀)
    (ψ : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback ρa).obj E') ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback τa).obj E₀))
    (hψ : pullbackIsoAlong ee ψ =
      (pullbackCompIso e1 (Iso.refl ((Scheme.Modules.pullback ρa).obj E'))).symm ≪≫
        pullbackCompIso (rfl : rQp ≫ rN = rQp ≫ rN) σ ≪≫ β ≪≫
        pullbackCompIso e2 (Iso.refl ((Scheme.Modules.pullback τa).obj E₀)))
    (hglue : pullbackCompIso hV e₀ = pullbackCompIso hU eU ≪≫ starIso ek e7 e8 ψ) :
    pullbackCompIso h0 e₀ =
      pullbackCompIso hp (pullbackCompIso hrU eU ≪≫
        ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ)) ≪≫ β := by
  have e'' : (rQp ≫ rU) ≫ ιU = bQ := by rw [Category.assoc, hrU, hp]
  have qk : q ≫ k = cA := by rw [← ek, ← Category.assoc, qt, ee]
  have ekk : q ≫ jU ≫ ρU = rQp ≫ rN := by rw [← Category.assoc, qU, Category.assoc, h5]
  have e6 : (rQp ≫ rU) ≫ ρU = rQp ≫ rN := by rw [Category.assoc, h5]
  have hL : pullbackCompIso h0 e₀ = pullbackCompIso e'' eU ≪≫
      (pullbackCompIso qU (Iso.refl _) ≪≫ (Scheme.Modules.pullback q).mapIso (starIso ek e7 e8 ψ) ≪≫
        (pullbackCompIso qV (Iso.refl ((Scheme.Modules.pullback jV).obj E₀))).symm) := by
    rw [pullbackCompIso_comp' q hV qV qW h0 e₀, hglue, Functor.mapIso_trans,
      pullbackCompIso_comp' q hU qU qW e'' eU]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  have hR : pullbackCompIso hp (pullbackCompIso hrU eU ≪≫
        ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ)) ≪≫ β =
      pullbackCompIso e'' eU ≪≫ (pullbackCompIso (rfl : rQp ≫ rU = rQp ≫ rU) (Iso.refl _) ≪≫
        (Scheme.Modules.pullback rQp).mapIso
          ((pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫ σ) ≪≫ β) := by
    rw [pullbackCompIso_trans_right, pullbackCompIso_comp' rQp hrU rfl hp e'' eU,
      pullbackCompIso_eq_refl_trans hp (pullbackCompIso hrU eU)]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [hL, hR]
  congr 1
  simp only [starIso, Functor.mapIso_trans, Functor.mapIso_symm]
  rw [mapIso_pullbackIsoAlong q ek ee qt qk ψ, hψ, mapIso_pullbackCompIso_refl q e7 qk ekk e1 E',
    mapIso_pullbackCompIso_refl q e8 qk qV e2 E₀,
    mapIso_pullbackCompIso_refl q (rfl : jU ≫ ρU = jU ≫ ρU) qU ekk e6 E',
    mapIso_pullbackCompIso_refl rQp h5 rfl rfl e6 E',
    pullbackCompIso_eq_refl_trans (rfl : rQp ≫ rN = rQp ≫ rN) σ]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id_assoc, Iso.trans_refl, Iso.self_symm_id, Iso.symm_self_id]

end

end GroundTheory.Heights₂.Heights.Model
