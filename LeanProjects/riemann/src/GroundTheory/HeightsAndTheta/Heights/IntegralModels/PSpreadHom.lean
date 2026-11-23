import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsInvOpenInsideRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

section Trans

variable {S T Y Z : Scheme.{0}}

lemma pullbackCompIso_trans {g₁ : S ⟶ T} {g₂ : T ⟶ Y} {h : Y ⟶ Z} {k₂ : T ⟶ Z} {k : S ⟶ Z}
    {g : S ⟶ Y} (e₂ : g₂ ≫ h = k₂) (e₁ : g₁ ≫ k₂ = k) (eg : g₁ ≫ g₂ = g) (e : g ≫ h = k)
    (M : Z.Modules) :
    (pullbackCompIso e₁ (Iso.refl _)).hom ≫
      (Scheme.Modules.pullback g₁).map
        (pullbackCompIso e₂ (Iso.refl ((Scheme.Modules.pullback h).obj M))).hom ≫
        (Scheme.Modules.pullbackComp g₁ g₂).hom.app _ ≫ (Scheme.Modules.pullbackCongr eg).hom.app _ =
      (pullbackCompIso e (Iso.refl _)).hom := by
  subst e₂ e₁ eg
  have H := congrArg (fun φ => φ.app M) (Scheme.Modules.pseudofunctor_associativity g₁ g₂ h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at H
  have H' : (Scheme.Modules.pullbackComp g₁ (g₂ ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback g₁).map ((Scheme.Modules.pullbackComp g₂ h).inv.app M) ≫
        (Scheme.Modules.pullbackComp g₁ g₂).hom.app _ =
      eqToHom (by simp) ≫ (Scheme.Modules.pullbackComp (g₁ ≫ g₂) h).inv.app M := by
    rw [← reassoc_of% H]
    simp
  simp only [pullbackCompIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Functor.mapIso_refl, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc, eqToIso.inv,
    eqToHom_app]
  simpa using H'

lemma pullbackHomAlong_trans {g₁ : S ⟶ T} {g₂ : T ⟶ Y} {h : Y ⟶ Z} {k₂ : T ⟶ Z} {k : S ⟶ Z}
    {g : S ⟶ Y} (e₂ : g₂ ≫ h = k₂) (e₁ : g₁ ≫ k₂ = k) (eg : g₁ ≫ g₂ = g) (e : g ≫ h = k)
    {F G : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G) :
    pullbackHomAlong e₁ (pullbackHomAlong e₂ ψ) = pullbackHomAlong e ψ := by
  have hF := pullbackCompIso_trans e₂ e₁ eg e F
  have hG := pullbackCompIso_trans e₂ e₁ eg e G
  subst eg
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] at hF hG
  have hG' : (pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback h).obj G))).inv =
      (Scheme.Modules.pullbackComp g₁ g₂).inv.app _ ≫
        (Scheme.Modules.pullback g₁).map (pullbackCompIso e₂ (Iso.refl _)).inv ≫
          (pullbackCompIso e₁ (Iso.refl _)).inv := by
    apply Iso.inv_ext
    rw [← hG]
    simp [← Functor.map_comp_assoc]
  unfold pullbackHomAlong
  rw [← hF, hG']
  have nat : (Scheme.Modules.pullbackComp g₁ g₂).hom.app _ ≫ (Scheme.Modules.pullback (g₁ ≫ g₂)).map ψ ≫
      (Scheme.Modules.pullbackComp g₁ g₂).inv.app _ =
      (Scheme.Modules.pullback g₁).map ((Scheme.Modules.pullback g₂).map ψ) := by
    rw [← (Scheme.Modules.pullbackComp g₁ g₂).hom.naturality_assoc ψ]
    simp
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nat]

end Trans

lemma invOpen_le_of_dvd {X : Scheme.{0}} (f : X ⟶ SpecZ) {m k : ℤ} (h : m ∣ k) :
    invOpen f k ≤ invOpen f m := by
  obtain ⟨c, rfl⟩ := h
  exact invOpen_mul_le_left f m c

theorem SpreadHom.proof (h₁ : SpreadHomNbhd.Statement) (h₂ : InvOpenInsideRat.Statement) :
    SpreadHom.Statement := by
  intro X f _ _ a ha F G hF hG φ
  obtain ⟨W, hWa, hW, ψ, hψ⟩ := h₁ X f a ha F G hF hG φ
  obtain ⟨m, hm, hmW⟩ := h₂ X f W hW
  refine ⟨m, hm, fun n hn hmn => ?_⟩
  have hle : invOpen f ((a : ℤ) * (n : ℤ)) ≤ W :=
    (invOpen_le_of_dvd f (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hmn) _)).trans hmW
  refine ⟨pullbackHomAlong (X.homOfLE_homOfLE hle hWa) ψ, ?_⟩
  rw [pullbackHomAlong_trans _ _ ?_ (toOpen_homOfLE f ℚ W hW
    (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) hWa)]
  · exact hψ
  · rw [← cancel_mono W.ι]
    simp [Scheme.homOfLE_ι]

end

end GroundTheory.Heights₂.Heights.Model
