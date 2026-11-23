import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

variable {T U W : Scheme.{u}}

noncomputable def pullbackSection (g : T ⟶ U) (N : U.Modules) :
    Γ(N, ⊤) →+ Γ((Scheme.Modules.pullback g).obj N, ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤).hom

lemma pullbackSection_smul (g : T ⟶ U) (N : U.Modules) (a : Γ(U, ⊤)) (n : Γ(N, ⊤)) :
    pullbackSection g N (a • n) = g.appTop a • pullbackSection g N n :=
  Scheme.Modules.Hom.app_smul _ a n

lemma pullbackSection_naturality (g : T ⟶ U) {N N' : U.Modules} (φ : N ⟶ N') (n : Γ(N, ⊤)) :
    ((Scheme.Modules.pullback g).map φ).app ⊤ (pullbackSection g N n) =
      pullbackSection g N' (φ.app ⊤ n) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ
  have h := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ ⊤).hom n) this
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h.symm

lemma pullbackComp_inv_pullbackSection (f : W ⟶ T) (g : T ⟶ U) (N : U.Modules) (n : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app N).app ⊤ (pullbackSection (f ≫ g) N n) =
      pullbackSection f _ (pullbackSection g N n) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ ⊤).hom n) h
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, Scheme.Modules.pushforwardComp_hom_app_app] at h'
  exact h'.symm

end GroundTheory.Arith.Etale
