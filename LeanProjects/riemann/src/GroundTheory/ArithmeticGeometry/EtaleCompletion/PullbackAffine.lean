import Mathlib
import GroundTheory.ArithmeticGeometry.EtaleCompletion.ModulesPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable def sectionLinear {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P') :
    Γ(P, ⊤) →ₗ[Γ(X, ⊤)] Γ(P', ⊤) where
  toFun := θ.app ⊤
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul θ

@[simp] lemma sectionLinear_apply {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P') (x : Γ(P, ⊤)) :
    sectionLinear θ x = θ.app ⊤ x := rfl

def IsBaseChangeSection {T U : Scheme.{u}} (g : T ⟶ U) (N : U.Modules) : Prop :=
  ∀ (Q : Type u) [AddCommGroup Q] [Module Γ(T, ⊤) Q] (ψ : Γ(N, ⊤) →+ Q),
    (∀ (a : Γ(U, ⊤)) (n : Γ(N, ⊤)), ψ (a • n) = g.appTop a • ψ n) →
    ∃! ψ' : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q,
      ∀ n, ψ' (pullbackSection g N n) = ψ n

lemma IsBaseChangeSection.comp {W T U : Scheme.{u}} {f : W ⟶ T} {g : T ⟶ U} {N : U.Modules}
    (hg : IsBaseChangeSection g N)
    (hf : IsBaseChangeSection f ((Scheme.Modules.pullback g).obj N)) :
    IsBaseChangeSection (f ≫ g) N := by
  intro Q _ _ ψ hψ
  let : Module Γ(T, ⊤) Q := Module.compHom Q f.appTop.hom
  have hsm : ∀ (t : Γ(T, ⊤)) (q : Q), t • q = f.appTop t • q := fun _ _ => rfl
  obtain ⟨ψ₁, hψ₁, u₁⟩ := hg Q ψ (fun a n => by
    rw [hψ, hsm, Scheme.Hom.comp_appTop]; rfl)
  obtain ⟨ψ₂, hψ₂, u₂⟩ := hf Q ψ₁.toAddMonoidHom (fun t x => ψ₁.map_smul t x)
  let c := (Scheme.Modules.pullbackComp f g).app N
  have hc : ∀ n, c.inv.app ⊤ (pullbackSection (f ≫ g) N n) =
      pullbackSection f _ (pullbackSection g N n) :=
    pullbackComp_inv_pullbackSection f g N
  have hchi : ∀ x, c.hom.app ⊤ (c.inv.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.inv_hom_id]; rfl
  have hchi' : ∀ x, c.inv.app ⊤ (c.hom.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.hom_inv_id]; rfl
  refine ⟨ψ₂ ∘ₗ sectionLinear c.inv, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · simp only [LinearMap.comp_apply, sectionLinear_apply, hc, hψ₂]
    exact hψ₁ n
  · let χ : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), ⊤) →ₗ[Γ(W, ⊤)] Q :=
      ψ'' ∘ₗ sectionLinear c.hom
    have hχ : ∀ n, χ (pullbackSection f _ (pullbackSection g N n)) = ψ n := fun n => by
      simp only [χ, LinearMap.comp_apply, sectionLinear_apply, ← hc, hchi, hψ'']
    let χ₁ : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q :=
      { toFun := fun x => χ (pullbackSection f _ x)
        map_add' := fun x y => by simp
        map_smul' := fun t x => by
          simp only [RingHom.id_apply]
          rw [pullbackSection_smul, map_smul, hsm] }
    have h₁ : χ₁ = ψ₁ := u₁ χ₁ hχ
    have h₂ : χ = ψ₂ := u₂ χ (fun x => congrArg (fun l => l x) h₁)
    ext x
    simp only [LinearMap.comp_apply, sectionLinear_apply, ← h₂, χ, hchi]

lemma bijective_map_of_isIso_counit {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (fun h : X ⟶ Y => G.map h) := by
  have : (fun h : X ⟶ Y => G.map h) =
      (adj.homEquiv (G.obj X) Y) ∘ (fun h => adj.counit.app X ≫ h) := by
    funext h
    simp [Adjunction.homEquiv_unit]
  rw [this]
  exact (adj.homEquiv _ _).bijective.comp
    ⟨fun a b h => (cancel_epi _).mp h,
      fun b => ⟨inv (adj.counit.app X) ≫ b, by simp⟩⟩

set_option backward.isDefEq.respectTransparency false in

lemma existsUnique_hom_app_top {A : CommRingCat.{u}} (P P' : (Spec A).Modules)
    [IsIso P.fromTildeΓ] (f : Γ(P, ⊤) →ₗ[Γ(Spec A, ⊤)] Γ(P', ⊤)) :
    ∃! θ : P ⟶ P', ∀ x, θ.app ⊤ x = f x := by
  have : IsIso ((tilde.adjunction (R := A)).counit.app P) :=
    inferInstanceAs (IsIso P.fromTildeΓ)
  have hb := bijective_map_of_isIso_counit (tilde.adjunction (R := A)) P P'
  let fA : (moduleSpecΓFunctor (R := A)).obj P ⟶ (moduleSpecΓFunctor (R := A)).obj P' :=
    ModuleCat.ofHom (X := (moduleSpecΓFunctor (R := A)).obj P)
      (Y := (moduleSpecΓFunctor (R := A)).obj P')
      { toFun := f
        map_add' := map_add f
        map_smul' := fun a x => f.map_smul ((Scheme.ΓSpecIso A).inv a) x }
  obtain ⟨θ, hθ⟩ := hb.2 fA
  refine ⟨θ, fun x => ?_, fun θ' hθ' => hb.1 ?_⟩
  · exact congrArg (fun l => l.hom x) hθ
  · refine hθ.symm ▸ ?_
    ext x
    exact hθ' x

lemma exists_modules_linearEquiv (R : CommRingCat.{u}) (Q : Type u) [AddCommGroup Q]
    [Module Γ(Spec R, ⊤) Q] :
    ∃ P : (Spec R).Modules, Nonempty (Γ(P, ⊤) ≃ₗ[Γ(Spec R, ⊤)] Q) := by
  let : Module R Q := Module.compHom Q (Scheme.ΓSpecIso R).inv.hom
  let e := (tilde.isoTop (ModuleCat.of R Q)).toLinearEquiv
  refine ⟨tilde (ModuleCat.of R Q), ⟨
    { toFun := e.symm
      invFun := e
      map_add' := map_add e.symm
      map_smul' := fun t x => ?_
      left_inv := fun x => e.apply_symm_apply x
      right_inv := fun x => e.symm_apply_apply x }⟩⟩
  obtain ⟨r, rfl⟩ : ∃ r : R, (Scheme.ΓSpecIso R).inv r = t :=
    ⟨(Scheme.ΓSpecIso R).hom t, by simp⟩
  exact e.symm.map_smul r x

noncomputable def pushforwardΓIso {A R : CommRingCat.{u}} (φ : A ⟶ R) :
    moduleSpecΓFunctor (R := R) ⋙ ModuleCat.restrictScalars φ.hom ≅
      Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := A) :=
  Iso.symm (Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)))

noncomputable def pullbackTildeIso {A R : CommRingCat.{u}} (φ : A ⟶ R) :
    tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor R :=
  ((tilde.adjunction (R := A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := R))).ofNatIsoRight
      (pushforwardΓIso φ))

lemma isIso_fromTildeΓ_pullback {A R : CommRingCat.{u}} (φ : A ⟶ R) (N : (Spec A).Modules)
    [IsIso N.fromTildeΓ] :
    IsIso ((Scheme.Modules.pullback (Spec.map φ)).obj N).fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff]
  exact ⟨_, ⟨((pullbackTildeIso φ).app _).symm ≪≫
    (Scheme.Modules.pullback (Spec.map φ)).mapIso (@asIso _ _ _ _ N.fromTildeΓ ‹_›)⟩⟩

lemma isBaseChangeSection_specMap {A R : CommRingCat.{u}} (φ : A ⟶ R) (N : (Spec A).Modules)
    [IsIso N.fromTildeΓ] : IsBaseChangeSection (Spec.map φ) N := by
  intro Q _ _ ψ hψ
  set g := Spec.map φ with hg
  have := isIso_fromTildeΓ_pullback φ N
  obtain ⟨P, ⟨e⟩⟩ := exists_modules_linearEquiv R Q
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let f : Γ(N, ⊤) →ₗ[Γ(Spec A, ⊤)] Γ((Scheme.Modules.pushforward g).obj P, ⊤) :=
    { toFun := fun n => e.symm (ψ n)
      map_add' := fun x y => by
        rw [map_add, map_add]
        rfl
      map_smul' := fun a x => by
        rw [hψ, map_smul]
        rfl }
  have hf : ∀ n, f n = e.symm (ψ n) := fun _ => rfl
  obtain ⟨θ, hθ, uθ⟩ := existsUnique_hom_app_top N _ f
  have key : ∀ (h : (Scheme.Modules.pullback g).obj N ⟶ P) (n : Γ(N, ⊤)),
      (adj.homEquiv _ _ h).app ⊤ n = h.app ⊤ (pullbackSection g N n) := fun h n => by
    rw [Adjunction.homEquiv_unit]
    rfl
  let θ' := (adj.homEquiv _ _).symm θ
  refine ⟨e.toLinearMap ∘ₗ sectionLinear θ', fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · have := key θ' n
    rw [Equiv.apply_symm_apply, hθ, hf] at this
    simp only [LinearMap.comp_apply, sectionLinear_apply, LinearEquiv.coe_coe]
    erw [← this]
    simp
  · obtain ⟨h, hh, -⟩ := existsUnique_hom_app_top _ P (e.symm.toLinearMap ∘ₗ ψ'')
    have : adj.homEquiv _ _ h = θ := uθ _ (fun n => by
      rw [key, hh, hf]
      simp [hψ''])
    have hθ' : h = θ' := by simp [θ', ← this]
    ext x
    simp [← hθ', hh]

lemma bijective_pullbackSection_of_isIso {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules) :
    Function.Bijective (pullbackSection g N) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction g) N
  have hU : (⊤ : U.Opens) ≤ g ''ᵁ (g ⁻¹ᵁ (⊤ : U.Opens)) := by
    simp [Scheme.Hom.opensRange_of_isIso]
  have h1 : IsIso (((Scheme.Modules.restrictAdjunction g).unit.app N).app ⊤) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have : IsIso (homOfLE (g.image_preimage_le (⊤ : U.Opens))).op :=
      ⟨(homOfLE hU).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    exact Functor.map_isIso N.presheaf _
  have h2 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤) := by
    rw [← h, Scheme.Modules.Hom.comp_app]
    have : IsIso (((Scheme.Modules.pushforward g).map
        (((Scheme.Modules.restrictAdjunction g).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction g)).hom.app N)).app ⊤) :=
      inferInstanceAs (IsIso (Scheme.Modules.Hom.app _ _))
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤)

lemma isBaseChangeSection_of_isIso {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules) :
    IsBaseChangeSection g N := by
  intro Q _ _ ψ hψ
  have hb := bijective_pullbackSection_of_isIso g N
  have : IsIso g.appTop := inferInstanceAs (IsIso (g.app ⊤))
  let e := AddEquiv.ofBijective (pullbackSection g N) hb
  have he : ∀ n, e.symm (pullbackSection g N n) = n := fun n => e.symm_apply_apply n
  have hs : ∀ x, pullbackSection g N (e.symm x) = x := fun x => e.apply_symm_apply x
  refine ⟨{ toFun := fun x => ψ (e.symm x)
            map_add' := fun x y => by simp
            map_smul' := fun t x => ?_ }, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a : Γ(U, ⊤), g.appTop a = t :=
      ⟨(asIso g.appTop).inv t, by simp⟩
    simp only [RingHom.id_apply]
    rw [← hψ, ← hs x, he, ← pullbackSection_smul, he]
  · simp [he]
  · ext x
    obtain ⟨n, rfl⟩ := hb.2 x
    simp [he, hψ'']

lemma isQuasicoherent_pullback_of_isIso {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules)
    [N.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj N).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback g).app N) inferInstance

theorem existsUnique_pullbackSection {T U : Scheme.{u}} (g : T ⟶ U) [IsAffine T] [IsAffine U]
    (N : U.Modules) [N.IsQuasicoherent] (Q : Type u) [AddCommGroup Q] [Module Γ(T, ⊤) Q]
    (ψ : Γ(N, ⊤) →+ Q) (hψ : ∀ (a : Γ(U, ⊤)) (n : Γ(N, ⊤)), ψ (a • n) = g.appTop a • ψ n) :
    ∃! ψ' : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q,
      ∀ n, ψ' (pullbackSection g N n) = ψ n := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = T.isoSpec.inv ≫ g ≫ U.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hg : g = T.isoSpec.hom ≫ Spec.map φ ≫ U.isoSpec.inv := by simp [hφ]
  have key : IsBaseChangeSection g N := by
    rw [hg]
    have := isQuasicoherent_pullback_of_isIso U.isoSpec.inv N
    have := (isQuasicoherent_iff_isIso_fromTildeΓ
      ((Scheme.Modules.pullback U.isoSpec.inv).obj N)).mp inferInstance
    exact IsBaseChangeSection.comp (IsBaseChangeSection.comp (isBaseChangeSection_of_isIso _ N)
      (isBaseChangeSection_specMap φ _)) (isBaseChangeSection_of_isIso _ _)
  exact key Q ψ hψ

end GroundTheory.Arith.Etale
