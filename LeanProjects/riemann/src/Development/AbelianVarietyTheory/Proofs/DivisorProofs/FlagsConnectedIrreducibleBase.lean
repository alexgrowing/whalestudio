import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldFlagsConjugateByAutomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsOverFieldIrreducibleJoinStatement
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.FlagConnect

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPath

open Scheme.Modules in

theorem coh {X T B : Scheme.{0}} (t : X ⟶ T) (c : T ⟶ X) (s : X ⟶ B) (h : t ≫ c = 𝟙 _) (v : t ≫ c ≫ s = s)
    (E : B.Modules) :
    (pullbackComp t c).hom.app ((pullback s).obj E) ≫
      (pullbackCongr h).hom.app _ ≫ (pullbackId _).hom.app _ =
    (pullback t).map ((pullbackComp c s).hom.app E) ≫
      (pullbackComp t (c ≫ s)).hom.app E ≫ (pullbackCongr v).hom.app E := by
  have assoc := congr_arg (fun φ => φ.app E) (pseudofunctor_associativity t c s)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id, eqToHom_app] at assoc
  have key : ∀ (u : X ⟶ X) (hu : u = 𝟙 X) (w : X ⟶ B) (hw : w = u ≫ s) (v' : w = s)
      (P : (pullback w).obj E = (pullback (u ≫ s)).obj E),
      eqToHom P ≫ (pullbackComp u s).inv.app E ≫ (pullbackCongr hu).hom.app _ ≫ (pullbackId X).hom.app _ =
        (pullbackCongr v').hom.app E := by
    intro u hu w hw v' P
    subst hu hw
    have unit := congr_arg (fun φ => φ.app E) (pseudofunctor_right_unitality s)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Category.comp_id, eqToHom_app] at unit
    simp only [eqToHom_refl, Category.id_comp, pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
    erw [Category.comp_id ((pullbackId X).hom.app ((pullback s).obj E))] at unit
    erw [Category.id_comp ((pullbackId X).hom.app ((pullback s).obj E))]
    erw [unit]
    simp [eqToIso.hom, eqToHom_app]
  have e1 : (pullbackComp t c).hom.app ((pullback s).obj E) =
      (pullback t).map ((pullbackComp c s).hom.app E) ≫ (pullbackComp t (c ≫ s)).hom.app E ≫
        eqToHom (by rw [Category.assoc]) ≫ (pullbackComp (t ≫ c) s).inv.app E := by
    rw [← cancel_epi ((pullbackComp t (c ≫ s)).inv.app E ≫ (pullback t).map ((pullbackComp c s).inv.app E)),
      ← cancel_mono ((pullbackComp (t ≫ c) s).hom.app E)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    simp
  rw [e1]
  simp only [Category.assoc]
  congr 2
  exact key _ h _ (Category.assoc _ _ _).symm v _

open Scheme.Modules in

theorem carries_of {X T B : Scheme.{0}} (s : X ⟶ B) (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X) {ι : Type}
    (E : ι → B.Modules) (r : ι → ℕ) (G₁ G' : ∀ a, Vert.Flag ((pullback s).obj (E a)) (r a))
    (Φ : ∀ a, (pullback c).obj ((pullback s).obj (E a)) ≅ (pullback c).obj ((pullback s).obj (E a)))
    (ψ : ∀ a, (pullback s).obj (E a) ≅ (pullback s).obj (E a))
    (hΦ : ∀ a, (pullback t).map (Φ a).hom ≫ (pullbackComp t c).hom.app _ ≫ (pullbackCongr h).hom.app _ ≫
      (pullbackId X).hom.app _ = ((pullbackComp t c).hom.app _ ≫ (pullbackCongr h).hom.app _ ≫
      (pullbackId X).hom.app _) ≫ (ψ a).hom)
    (hψ : ∀ a i, ∃ e : (G₁ a).F i ≅ (G' a).F i, e.hom ≫ (G' a).ι i = (G₁ a).ι i ≫ (ψ a).hom)
    (v : t ≫ c ≫ s = s) :
    Carries (c ≫ s) E r (fun a => ((G₁ a).pull c).ofIso (Φ a ≪≫ (pullbackComp c s).app (E a))) t s v G' := by
  intro a i
  obtain ⟨e, he⟩ := hψ a i
  refine ⟨(pullbackComp t c).app _ ≪≫ (pullbackCongr h).app _ ≪≫ (pullbackId X).app _ ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, he]
  simp only [Vert.Flag.ofIso, Vert.Flag.pull, Functor.map_comp, Category.assoc, Iso.trans_hom, Iso.app_hom]
  rw [← coh t c s h v (E a)]
  simp only [Category.assoc] at hΦ
  rw [hΦ a, he]
  erw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  rfl

theorem exists_irreducible_family : ∀ (L : Type) [Field L] (B : Scheme.{0}) (s : Spec (CommRingCat.of L) ⟶ B)
    (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (G₁ G₂ : ∀ a, Vert.Flag ((Scheme.Modules.pullback s).obj (E a)) (r a)),
    ∃ (T : Scheme.{0}) (g : T ⟶ B) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T)
      (G : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)) (v₁ : t₁ ≫ g = s) (v₂ : t₂ ≫ g = s),
      IrreducibleSpace T ∧ Carries g E r G t₁ s v₁ G₁ ∧ Carries g E r G t₂ s v₂ G₂ := by
  intro L _ B s ι _ E r G₁ G₂
  choose φ hφ using fun a => GlobalTheory.T.field_flags_conjugate_by_automorphism L _ (r a) (G₁ a) (G₂ a)
  obtain ⟨T, c, t₁, t₂, h₁, h₂, Φ, hT, hΦ₁, hΦ₂⟩ := GlobalTheory.T.flags_over_field_irreducible_join L ι
    (fun a => (Scheme.Modules.pullback s).obj (E a)) r (fun a => (G₁ a).isVB_self) φ
  have v₁ : t₁ ≫ c ≫ s = s := by rw [← Category.assoc, h₁, Category.id_comp]
  have v₂ : t₂ ≫ c ≫ s = s := by rw [← Category.assoc, h₂, Category.id_comp]
  refine ⟨T, c ≫ s, t₁, t₂, fun a => ((G₁ a).pull c).ofIso (Φ a ≪≫ (Scheme.Modules.pullbackComp c s).app (E a)),
    v₁, v₂, hT, ?_, ?_⟩
  · exact carries_of s c t₁ h₁ E r G₁ G₁ Φ (fun _ => Iso.refl _) (fun a => by rw [hΦ₁ a]; simp)
      (fun _ _ => ⟨Iso.refl _, by simp⟩) v₁
  · exact carries_of s c t₂ h₂ E r G₁ G₂ Φ φ hΦ₂ hφ v₂

end GlobalTheory.FlagPath

end
