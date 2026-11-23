import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SupportMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

section Spec

variable {R : CommRingCat.{u}} {M N : (Spec (.of R)).Modules} (ψ : M ⟶ N)

def cokernelTildeIso (hM : IsIso M.fromTildeΓ) (hN : IsIso N.fromTildeΓ) :
    (tilde.functor R).obj (cokernel (moduleSpecΓFunctor.map ψ)) ≅ cokernel ψ :=
  let p : (moduleSpecΓFunctor ⋙ tilde.functor R).obj M ≅ M := @asIso _ _ _ _ M.fromTildeΓ hM
  let q : (moduleSpecΓFunctor ⋙ tilde.functor R).obj N ≅ N := @asIso _ _ _ _ N.fromTildeΓ hN
  PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map ψ) ≪≫
    cokernel.mapIso ((moduleSpecΓFunctor ⋙ tilde.functor R).map ψ) ψ p q
      (Scheme.Modules.fromTildeΓNatTrans.naturality ψ)

lemma cokernelTildeIso_comm (hM : IsIso M.fromTildeΓ) (hN : IsIso N.fromTildeΓ) :
    (tilde.functor R).map (cokernel.π (moduleSpecΓFunctor.map ψ)) ≫
      (cokernelTildeIso ψ hM hN).hom = N.fromTildeΓ ≫ cokernel.π ψ := by
  have h : (tilde.functor R).map (cokernel.π (moduleSpecΓFunctor.map ψ)) ≫
      (PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map ψ)).hom =
      cokernel.π ((tilde.functor R).map (moduleSpecΓFunctor.map ψ)) := by
    rw [← π_comp_cokernelComparison, ← PreservesCokernel.iso_inv, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [cokernelTildeIso, Iso.trans_hom, ← Category.assoc, h]
  simp [cokernel.mapIso]
  try rfl

lemma isQuasicoherent_cokernel_spec [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel ψ).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (.of R)).ringCatSheaf).prop_of_iso
    (cokernelTildeIso ψ inferInstance inferInstance)
    (inferInstanceAs ((tilde.functor R).obj _).IsQuasicoherent)

lemma surjective_cokernel_π_app_top [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective ((cokernel.π ψ).app ⊤) := by
  have hM : IsIso M.fromTildeΓ := inferInstance
  have hN : IsIso N.fromTildeΓ := inferInstance
  set Q := cokernel (moduleSpecΓFunctor.map ψ)
  set q := cokernel.π (moduleSpecΓFunctor.map ψ)
  have hq : Function.Surjective q := (ModuleCat.epi_iff_surjective q).1 inferInstance
  have h1 : Function.Surjective (((tilde.functor R).map q).app ⊤) := by
    have e := tilde.toOpen_map_app q ⊤
    intro y
    obtain ⟨y', rfl⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen Q ⊤)).2 y
    obtain ⟨z, rfl⟩ := hq y'
    refine ⟨tilde.toOpen _ ⊤ z, ?_⟩
    have := congrArg (fun g => g.hom z) e
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  have h2 : ∀ x, (cokernelTildeIso ψ hM hN).hom.app ⊤ (((tilde.functor R).map q).app ⊤ x) =
      (cokernel.π ψ).app ⊤ (N.fromTildeΓ.app ⊤ x) := fun x => by
    have := congrArg (fun g => (g.app ⊤) x) (cokernelTildeIso_comm ψ hM hN)
    exact this
  intro y
  obtain ⟨x, hx⟩ := ((ConcreteCategory.bijective_of_isIso
    ((cokernelTildeIso ψ hM hN).hom.app ⊤)).2.comp h1) y
  exact ⟨N.fromTildeΓ.app ⊤ x, (h2 x).symm.trans hx⟩

end Spec

section Scheme

variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G)

lemma bijective_app_of_iso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Function.Bijective (e.hom.app U) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app U, fun x => ?_, fun y => ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl

lemma isQuasicoherent_restrict_cokernel [F.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) : ((cokernel φ).restrict hU.fromSpec).IsQuasicoherent := by
  let Rf := Scheme.Modules.restrictFunctor hU.fromSpec
  have : (Rf.obj F).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have : (Rf.obj G).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have h := isQuasicoherent_cokernel_spec (R := Γ(X, U)) (Rf.map φ)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso Rf φ).symm h

instance isQuasicoherent_cokernel [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (cokernel φ).IsQuasicoherent :=
  isQuasicoherent_of_restrict (cokernel φ) (fun U : X.affineOpens => (U : X.Opens))
    (iSup_affineOpens_eq_top X)
    fun U => nonempty_presentation_restrict _ U.2 (isQuasicoherent_restrict_cokernel φ U.2)

lemma surjective_cokernel_π_app [F.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Surjective ((cokernel.π φ).app U) := by
  let Rf := Scheme.Modules.restrictFunctor hU.fromSpec
  have : (Rf.obj F).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have : (Rf.obj G).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have h1 := surjective_cokernel_π_app_top (R := Γ(X, U)) (Rf.map φ)
  have h2 : Rf.map (cokernel.π φ) = cokernel.π (Rf.map φ) ≫ (PreservesCokernel.iso Rf φ).inv := by
    rw [PreservesCokernel.iso_inv, π_comp_cokernelComparison]
  have h3 : Function.Surjective ((Rf.map (cokernel.π φ)).app ⊤) := by
    rw [h2]
    exact (bijective_app_of_iso (PreservesCokernel.iso Rf φ).symm ⊤).2.comp h1
  rw [← fromSpec_image_top hU]
  exact h3

theorem isCoherent_cokernel [F.IsQuasicoherent] (hG : IsCoherent G) :
    IsCoherent (cokernel φ) := by
  have := hG.1
  refine ⟨inferInstance, fun U hU => ?_⟩
  have := hG.2 U hU
  let π' : Γ(G, U) →ₗ[Γ(X, U)] Γ(cokernel φ, U) :=
    { toFun := (cokernel.π φ).app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  exact Module.Finite.of_surjective π' (surjective_cokernel_π_app φ hU)

end Scheme

section Sequences

variable {C : Type*} [Category C] [Abelian C] {P Q : C} (α : P ⟶ Q)

def kerCoimSC : ShortComplex C :=
  ShortComplex.mk (kernel.ι α) (Abelian.coimage.π α) (cokernel.condition _)

lemma kerCoimSC_shortExact : (kerCoimSC α).ShortExact :=
  ShortComplex.ShortExact.mk' ((kerCoimSC α).exact_of_g_is_cokernel
    (cokernelIsCokernel (kernel.ι α))) (inferInstanceAs (Mono (kernel.ι α)))
    (inferInstanceAs (Epi (Abelian.coimage.π α)))

def coimCokSC : ShortComplex C :=
  ShortComplex.mk (Abelian.factorThruCoimage α) (cokernel.π α) (by
    rw [← cancel_epi (Abelian.coimage.π α), ← Category.assoc, Abelian.coimage.fac, comp_zero,
      cokernel.condition])

def coimCokIsColimit :
    IsColimit (CokernelCofork.ofπ (f := Abelian.factorThruCoimage α) (cokernel.π α)
      (coimCokSC α).zero) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun b hb => cokernel.desc α b (by
      rw [← Abelian.coimage.fac α, Category.assoc, hb, comp_zero]))
    (fun b hb => cokernel.π_desc _ _ _)
    (fun b hb m hm => by
      exact (cancel_epi (cokernel.π α)).1 (by rw [hm, cokernel.π_desc]))

lemma coimCokSC_shortExact : (coimCokSC α).ShortExact :=
  ShortComplex.ShortExact.mk' ((coimCokSC α).exact_of_g_is_cokernel (coimCokIsColimit α))
    (inferInstanceAs (Mono (Abelian.factorThruCoimage α))) (inferInstanceAs (Epi (cokernel.π α)))

end Sequences

end

end GroundTheory.Arith.SchemeCoh
