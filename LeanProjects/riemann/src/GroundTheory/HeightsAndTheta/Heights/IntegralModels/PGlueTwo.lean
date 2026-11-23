import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlueTwo
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueModulesStar
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.GlueCoherence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlueTwo

lemma pullbackCompIso_symm_trans {A B C Z : Scheme.{0}} {t : A ⟶ B} {s : B ⟶ C} {ι : C ⟶ Z}
    {j : B ⟶ Z} {u : A ⟶ C} {w : A ⟶ Z} (e : s ≫ ι = j) (eg : t ≫ s = u) (ek : t ≫ j = w)
    (e' : u ≫ ι = w) {E : Z.Modules} {F : B.Modules} (a : (Scheme.Modules.pullback j).obj E ≅ F) :
    pullbackCompIso eg ((pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫ a) =
      (pullbackCompIso e' (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫
        pullbackCompIso ek a := by
  rw [pullbackCompIso_comp' t e eg ek e' (Iso.refl ((Scheme.Modules.pullback ι).obj E)),
    pullbackCompIso_eq_refl_trans eg
      ((pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫ a),
    pullbackCompIso_eq_refl_trans ek a, Functor.mapIso_trans, Functor.mapIso_symm]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem proof : GlueTwo.Statement := by
  intro X O₁ O₂ O O₁₂ h₁ h₂ _ k₁ k₂ hk F₁ F₂ ψ
  obtain rfl : O₁ ⊓ O₂ = O₁₂ := le_antisymm hk (le_inf k₁ k₂)
  let I := GlueModulesStar.index O₂ (fun _ : Unit => O₁) F₂ (fun _ => F₁) (fun _ => ψ)
  have h0 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction O₂.ι).homEquiv _ _).symm
      (Multiequalizer.ι I none)) :=
    GlueModulesStar.isIso_homEquiv_symm O₂.ι _ (fun W =>
      GlueModulesStar.isIso_ι_none_app O₂ (fun _ : Unit => O₁) F₂ (fun _ => F₁) (fun _ => ψ) _
        (O₂.ι_image_le W))
  have hi : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction O₁.ι).homEquiv _ _).symm
      (Multiequalizer.ι I (some ()))) :=
    GlueModulesStar.isIso_homEquiv_symm O₁.ι _ (fun W =>
      GlueModulesStar.isIso_ι_some_app O₂ (fun _ : Unit => O₁) F₂ (fun _ => F₁) (fun _ => ψ)
        (fun i j hij => absurd (Subsingleton.elim i j) hij) () _ (O₁.ι_image_le W))
  let a₂ := asIso (((Scheme.Modules.pullbackPushforwardAdjunction O₂.ι).homEquiv _ _).symm
    (Multiequalizer.ι I none))
  let a₁ := asIso (((Scheme.Modules.pullbackPushforwardAdjunction O₁.ι).homEquiv _ _).symm
    (Multiequalizer.ι I (some ())))
  have hc : pullbackCompIso (X.homOfLE_ι k₂) a₂ = pullbackCompIso (X.homOfLE_ι k₁) a₁ ≪≫ ψ := by
    ext1
    apply ((Scheme.Modules.pullbackPushforwardAdjunction (O₁ ⊓ O₂).ι).homEquiv _ _).injective
    have e1 := GlueModulesStar.homEquiv_pullbackCompIso (X.homOfLE_ι k₂) a₂ (𝟙 _)
    have e2 := GlueModulesStar.homEquiv_pullbackCompIso (X.homOfLE_ι k₁) a₁ ψ.hom
    rw [Category.comp_id] at e1
    rw [Iso.trans_hom, e1, e2]
    simp only [a₁, a₂, asIso_hom, Equiv.apply_symm_apply]
    exact Multiequalizer.condition I ()
  refine ⟨(Scheme.Modules.pullback O.ι).obj (multiequalizer I),
    (pullbackCompIso (X.homOfLE_ι h₁) (Iso.refl _)).symm ≪≫ a₁,
    (pullbackCompIso (X.homOfLE_ι h₂) (Iso.refl _)).symm ≪≫ a₂, ?_⟩
  rw [pullbackCompIso_symm_trans (X.homOfLE_ι h₂) (X.homOfLE_homOfLE k₂ h₂) (X.homOfLE_ι k₂)
      (X.homOfLE_ι _),
    pullbackCompIso_symm_trans (X.homOfLE_ι h₁) (X.homOfLE_homOfLE k₁ h₁) (X.homOfLE_ι k₁)
      (X.homOfLE_ι _), hc, Iso.trans_assoc]

end GlueTwo

end

end GroundTheory.Heights₂.Heights.Model
