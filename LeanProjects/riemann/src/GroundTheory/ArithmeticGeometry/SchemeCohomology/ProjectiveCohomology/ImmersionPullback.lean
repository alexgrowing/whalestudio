import Mathlib
import GroundTheory.ArithmeticGeometry.EtaleCompletion.QcohZariski
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res pullbackUnitApp_comp
  pullbackUnitApp_comp_hom pullbackUnitApp_bijective)

universe u

noncomputable section

variable {Y Z : Scheme.{u}}

lemma pullbackUnitApp_smul (f : Y ⟶ Z) (N : Z.Modules) (O : Z.Opens) (r : Γ(Z, O))
    (n : Γ(N, O)) : pullbackUnitApp f N O (r • n) = f.app O r • pullbackUnitApp f N O n :=
  Scheme.Modules.Hom.app_smul _ r n

instance final_opensMap (f : Y ⟶ Z) : (Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, rfl⟩)

set_option backward.isDefEq.respectTransparency.types false in

def pullbackUnitIso (f : Y ⟶ Z) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Z.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  let e := asIso (C := SheafOfModules Y.ringCatSheaf)
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

def unitOne (Z : Scheme.{u}) (O : Z.Opens) : Γ(SheafOfModules.unit Z.ringCatSheaf, O) :=
  (1 : Γ(Z, O))

lemma pullbackUnitApp_naturality (f : Y ⟶ Z) {N N' : Z.Modules} (φ : N ⟶ N') (O : Z.Opens)
    (n : Γ(N, O)) :
    ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ O) (pullbackUnitApp f N O n) =
      pullbackUnitApp f N' O (φ.app O n) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ
  have h := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ O).hom n) this
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency.types false in

lemma pullbackUnitIso_hom_one (f : Y ⟶ Z) :
    (pullbackUnitIso f).hom.app ⊤
      (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤)) = unitOne Y ⊤ := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (fun ψ => ψ.val.app (op ⊤) (1 : Z.ringCatSheaf.obj.obj (op ⊤))) h
  simp only [SheafOfModules.unitToPushforwardObjUnit_val_app_apply, map_one] at h'
  exact h'

lemma isBasisOn_pullbackUnitApp_one (f : Y ⟶ Z) :
    IsBasisOn ((preMod Y).obj ((Scheme.Modules.pullback f).obj
      (SheafOfModules.unit Z.ringCatSheaf))) ⊤
      (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤)) := by
  have hb : IsBasisOn ((preMod Y).obj (SheafOfModules.unit Y.ringCatSheaf)) ⊤ (unitOne Y ⊤) :=
    isBasisOn_one ⊤
  have h2 := hb.map_iso (pullbackUnitIso f).symm
  have hx : ((preMod Y).map (pullbackUnitIso f).symm.hom).app (op ⊤)
      ((pullbackUnitIso f).hom.app ⊤
        (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤))) =
      pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤) := by
    have e2 := congrArg (fun φ => (Scheme.Modules.Hom.app φ ⊤).hom
      (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤)))
      (pullbackUnitIso f).hom_inv_id
    exact e2
  rw [← pullbackUnitIso_hom_one f, hx] at h2
  exact h2

lemma isBasisOn_pullbackUnitApp_of_top (f : Y ⟶ Z) {N : Z.Modules} {O : Z.Opens} (hO : ⊤ ≤ O)
    {t : Γ(N, O)} (ht : IsBasisOn ((preMod Z).obj N) O t) :
    IsBasisOn ((preMod Y).obj ((Scheme.Modules.pullback f).obj N)) (f ⁻¹ᵁ O)
      (pullbackUnitApp f N O t) := by
  obtain rfl : O = ⊤ := top_le_iff.mp hO
  let sec : N.val.sections := ⟨fun j => resM ((preMod Z).obj N) (le_top : j.unop ≤ ⊤) t,
    fun {j j'} g => by
      exact resM_resM _ _ _ _⟩
  let f₀ : 𝟙_ Z.Modules ⟶ N :=
    (SheafOfModules.unitHomEquiv N).symm sec
  have hf₀ : ∀ U : Z.Opens, Scheme.Modules.Hom.app f₀ U (unitOne Z U) = resM ((preMod Z).obj N) (le_top : U ≤ ⊤) t := by
    intro U
    have := SheafOfModules.unitHomEquiv_apply_coe N f₀ (op U)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have hf₀t : Scheme.Modules.Hom.app f₀ ⊤ (unitOne Z ⊤) = t := by
    rw [hf₀]
    exact resM_refl _ t
  have : IsIso f₀ := isIso_of_isBasisOn f₀ (fun _ => ⟨⊤, trivial, unitOne Z ⊤,
    isBasisOn_one ⊤, by
      change IsBasisOn _ ⊤ (Scheme.Modules.Hom.app f₀ ⊤ (unitOne Z ⊤))
      rw [hf₀t]
      exact ht⟩)
  have h2 := (isBasisOn_pullbackUnitApp_one f).map_iso (asIso ((Scheme.Modules.pullback f).map f₀))
  have hx : ((preMod Y).map (asIso ((Scheme.Modules.pullback f).map f₀)).hom).app (op ⊤)
      (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤)) =
      pullbackUnitApp f N ⊤ t := by
    change Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map f₀) (f ⁻¹ᵁ ⊤)
      (pullbackUnitApp f (𝟙_ Z.Modules) ⊤ (unitOne Z ⊤)) = _
    rw [pullbackUnitApp_naturality, hf₀t]
  rw [hx] at h2
  exact h2

abbrev appR (j : Y ⟶ Z) (V : Z.Opens) : ringOn Z V →+* ringOn Y (j ⁻¹ᵁ V) := (j.app V).hom

lemma pullbackUnitApp_smul_resM (j : Y ⟶ Z) (N : Z.Modules) {O V : Z.Opens} (h : V ≤ O)
    (r : ringOn Z V) (t : Γ(N, O)) :
    pullbackUnitApp j N V (r • resM ((preMod Z).obj N) h t) =
      appR j V r • resM ((preMod Y).obj ((Scheme.Modules.pullback j).obj N))
        ((Opens.map j.base).monotone h) (pullbackUnitApp j N O t) := by
  have e1 := pullbackUnitApp_smul j N V r (resM ((preMod Z).obj N) h t)
  have e2 := pullbackUnitApp_res j N (homOfLE h) t
  exact e1.trans (congrArg _ e2)

lemma isBasisOn_pullbackUnitApp_iff (j : Y ⟶ Z) [IsOpenImmersion j] (N : Z.Modules) {O : Z.Opens}
    (hO : O ≤ j.opensRange) (t : Γ(N, O)) :
    IsBasisOn ((preMod Y).obj ((Scheme.Modules.pullback j).obj N)) (j ⁻¹ᵁ O)
        (pullbackUnitApp j N O t) ↔ IsBasisOn ((preMod Z).obj N) O t := by
  have key : ∀ (V : Z.Opens) (h : V ≤ O),
      Function.Bijective (fun r : ringOn Y (j ⁻¹ᵁ V) =>
        r • resM ((preMod Y).obj ((Scheme.Modules.pullback j).obj N))
          ((Opens.map j.base).monotone h) (pullbackUnitApp j N O t)) ↔
      Function.Bijective (fun r : ringOn Z V => r • resM ((preMod Z).obj N) h t) := by
    intro V h
    have hV : V ≤ j.opensRange := h.trans hO
    have b1 : Function.Bijective (appR j V) := by
      have := Scheme.Hom.isIso_app j V hV
      exact ConcreteCategory.bijective_of_isIso _
    have b2 := pullbackUnitApp_bijective j N hV
    have comm : (fun r : ringOn Y (j ⁻¹ᵁ V) =>
        r • resM ((preMod Y).obj ((Scheme.Modules.pullback j).obj N))
          ((Opens.map j.base).monotone h) (pullbackUnitApp j N O t)) ∘ appR j V =
        pullbackUnitApp j N V ∘ (fun r : ringOn Z V => r • resM ((preMod Z).obj N) h t) := by
      funext r
      exact (pullbackUnitApp_smul_resM j N h r t).symm
    constructor
    · intro hl
      have := hl.comp b1
      rw [comm] at this
      exact (Function.Bijective.of_comp_iff' b2 _).1 this
    · intro hr
      have := b2.comp hr
      rw [← comm] at this
      exact (Function.Bijective.of_comp_iff _ b1).1 this
  constructor
  · intro hb V h
    exact (key V h).1 (hb (j ⁻¹ᵁ V) ((Opens.map j.base).monotone h))
  · intro hb V' h'
    obtain ⟨V, hVO, rfl⟩ : ∃ V, V ≤ O ∧ V' = j ⁻¹ᵁ V :=
      ⟨j ''ᵁ V', (j.image_mono h').trans (j.image_preimage_le O), (j.preimage_image_eq V').symm⟩
    exact (key V hVO).2 (hb V hVO)

lemma isBasisOn_pullbackUnitApp_comp {T : Scheme.{u}} (c : T ⟶ Y) (d : Y ⟶ Z) (N : Z.Modules)
    (O : Z.Opens) (t : Γ(N, O))
    (h : IsBasisOn ((preMod T).obj ((Scheme.Modules.pullback (c ≫ d)).obj N)) ((c ≫ d) ⁻¹ᵁ O)
      (pullbackUnitApp (c ≫ d) N O t)) :
    IsBasisOn ((preMod T).obj ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj N)))
      (c ⁻¹ᵁ (d ⁻¹ᵁ O)) (pullbackUnitApp c _ (d ⁻¹ᵁ O) (pullbackUnitApp d N O t)) := by
  have h2 := h.map_iso ((Scheme.Modules.pullbackComp c d).app N).symm
  have e := GroundTheory.Arith.Etale.pullbackUnitApp_comp c d N O t
  change IsBasisOn _ _ (((Scheme.Modules.pullbackComp c d).inv.app N).app ((c ≫ d) ⁻¹ᵁ O)
    (pullbackUnitApp (c ≫ d) N O t)) at h2
  rw [e] at h2
  exact h2

lemma isBasisOn_of_pullbackUnitApp_comp {T : Scheme.{u}} (c : T ⟶ Y) (d : Y ⟶ Z) (N : Z.Modules)
    (O : Z.Opens) (t : Γ(N, O))
    (h : IsBasisOn ((preMod T).obj
      ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj N)))
      (c ⁻¹ᵁ (d ⁻¹ᵁ O)) (pullbackUnitApp c _ (d ⁻¹ᵁ O) (pullbackUnitApp d N O t))) :
    IsBasisOn ((preMod T).obj ((Scheme.Modules.pullback (c ≫ d)).obj N)) ((c ≫ d) ⁻¹ᵁ O)
      (pullbackUnitApp (c ≫ d) N O t) := by
  have h2 := h.map_iso ((Scheme.Modules.pullbackComp c d).app N)
  have e := GroundTheory.Arith.Etale.pullbackUnitApp_comp_hom c d N O t
  change IsBasisOn _ _ (((Scheme.Modules.pullbackComp c d).hom.app N).app ((c ≫ d) ⁻¹ᵁ O)
    (pullbackUnitApp c _ (d ⁻¹ᵁ O) (pullbackUnitApp d N O t))) at h2
  rw [e] at h2
  exact h2

theorem isBasisOn_pullbackUnitApp (f : Y ⟶ Z) {N : Z.Modules} {W : Z.Opens} {t : Γ(N, W)}
    (ht : IsBasisOn ((preMod Z).obj N) W t) :
    IsBasisOn ((preMod Y).obj ((Scheme.Modules.pullback f).obj N)) (f ⁻¹ᵁ W)
      (pullbackUnitApp f N W t) := by

  have h1 : IsBasisOn ((preMod W.toScheme).obj ((Scheme.Modules.pullback W.ι).obj N)) (W.ι ⁻¹ᵁ W)
      (pullbackUnitApp W.ι N W t) :=
    (isBasisOn_pullbackUnitApp_iff W.ι N (by rw [Scheme.Opens.opensRange_ι]) t).2 ht

  have h2 := isBasisOn_pullbackUnitApp_of_top (f ∣_ W) (by rw [Scheme.Opens.ι_preimage_self]) h1
  have h3 := isBasisOn_of_pullbackUnitApp_comp (f ∣_ W) W.ι N W t h2
  rw [morphismRestrict_ι] at h3
  have h4 := isBasisOn_pullbackUnitApp_comp (f ⁻¹ᵁ W).ι f N W t h3
  exact (isBasisOn_pullbackUnitApp_iff (f ⁻¹ᵁ W).ι _ (by rw [Scheme.Opens.opensRange_ι]) _).1 h4

end

end GroundTheory.Arith.SchemeCoh
