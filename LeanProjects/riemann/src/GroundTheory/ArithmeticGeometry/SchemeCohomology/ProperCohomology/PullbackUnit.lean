import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Support
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
import GroundTheory.ArithmeticGeometry.EtaleCompletion.PullbackAffine
import GroundTheory.ArithmeticGeometry.EtaleCompletion.QcohZariski
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

section Affine

variable {X : Scheme.{u}}

lemma isIso_of_bijective_app_affine {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.Opens, IsAffineOpen U → Function.Bijective (f.app U)) : IsIso f := by
  have hB : Opens.IsBasis (Set.range fun U : X.affineOpens => (U : X.Opens)) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  have : IsIso (modulesAbMap f) := TopCat.Sheaf.isIso_iff_isIso_basis hB
    fun U => (ConcreteCategory.isIso_iff_bijective _).2 (h U.1 U.2)
  refine isIso_of_bijective_app f fun U => ?_
  have h1 : IsIso ((sheafToPresheaf _ _).map (modulesAbMap f)) := inferInstance
  have h2 := NatIso.isIso_app_of_isIso ((sheafToPresheaf _ _).map (modulesAbMap f)) (op U)
  exact (ConcreteCategory.isIso_iff_bijective _).1 h2

lemma bijective_app_of_bijective_app_affine {M N : X.Modules} (f : M ⟶ N) (W : X.Opens)
    (h : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → Function.Bijective (f.app V)) :
    ∀ V ≤ W, Function.Bijective (f.app V) := by
  have hR : IsIso ((Scheme.Modules.restrictFunctor W.ι).map f) :=
    isIso_of_bijective_app_affine _ fun V' hV' =>
      h _ (hV'.image_of_isOpenImmersion W.ι) ((W.ι.image_le_opensRange V').trans (by simp))
  intro V hV
  have hE : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hV
  rw [← hE]
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctor W.ι).map f).app (W.ι ⁻¹ᵁ V))

end Affine

section Section

variable {T U : Scheme.{u}}

theorem bijective_pullbackSection_of_surjective (g : T ⟶ U) [IsAffine T] [IsAffine U]
    (N : U.Modules) [N.IsQuasicoherent] (hg : Function.Surjective g.appTop)
    (hker : ∀ a : Γ(U, ⊤), g.appTop a = 0 → ∀ n : Γ(N, ⊤), a • n = 0) :
    Function.Bijective (Etale.pullbackSection g N) := by
  constructor
  · let K := RingHom.ker g.appTop.hom
    have hM : Module.IsTorsionBySet Γ(U, ⊤) Γ(N, ⊤) (K : Set Γ(U, ⊤)) :=
      fun n a => hker a.1 a.2 n
    let _ : Module (Γ(U, ⊤) ⧸ K) Γ(N, ⊤) := hM.module
    let e := RingHom.quotientKerEquivOfSurjective (f := g.appTop.hom) hg
    let _ : Module Γ(T, ⊤) Γ(N, ⊤) := Module.compHom _ e.symm.toRingHom
    obtain ⟨ψ', hψ', -⟩ := Etale.existsUnique_pullbackSection g N Γ(N, ⊤) (AddMonoidHom.id _)
      (fun a n => by
        change a • n = e.symm (g.appTop a) • n
        have he : e.symm (g.appTop a) = Ideal.Quotient.mk K a :=
          e.symm_apply_eq.2 (RingHom.quotientKerEquivOfSurjective_apply_mk hg a).symm
        rw [he, hM.mk_smul])
    intro x y hxy
    have := congrArg ψ' hxy
    rwa [hψ', hψ'] at this
  · intro p
    let P := Γ((Scheme.Modules.pullback g).obj N, ⊤)
    let L : Submodule Γ(T, ⊤) P := Submodule.span Γ(T, ⊤) (Set.range (Etale.pullbackSection g N))
    have hL : L = ⊤ := by
      obtain ⟨ψ', -, huniq⟩ := Etale.existsUnique_pullbackSection g N (P ⧸ L) 0
        (fun a n => by simp)
      have h0 : (0 : P →ₗ[Γ(T, ⊤)] (P ⧸ L)) = ψ' := huniq 0 (fun n => by simp)
      have h1 : L.mkQ = ψ' := huniq L.mkQ (fun n => by
        simpa using (Submodule.Quotient.mk_eq_zero L).2 (Submodule.subset_span ⟨n, rfl⟩))
      rw [eq_top_iff]
      intro q _
      have := LinearMap.congr_fun (h1.trans h0.symm) q
      exact (Submodule.Quotient.mk_eq_zero L).1 this
    have hp : p ∈ L := hL ▸ Submodule.mem_top
    induction hp using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | smul s x _ hx =>
      obtain ⟨n, rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hg s
      exact ⟨a • n, Etale.pullbackSection_smul g N a n⟩

end Section

section Move

variable {V T U : Scheme.{u}}

lemma bijective_pullbackUnitApp_comp_left_iff (f : V ⟶ T) [IsOpenImmersion f] (g : T ⟶ U)
    (N : U.Modules) (O : U.Opens) (hO : g ⁻¹ᵁ O ≤ f.opensRange) :
    Function.Bijective (Etale.pullbackUnitApp (f ≫ g) N O) ↔
      Function.Bijective (Etale.pullbackUnitApp g N O) := by
  have hc := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp f g).inv.app N).app ((f ≫ g) ⁻¹ᵁ O))
  have hf := Etale.pullbackUnitApp_bijective f ((Scheme.Modules.pullback g).obj N) hO
  have e : ⇑(ConcreteCategory.hom
      (((Scheme.Modules.pullbackComp f g).inv.app N).app ((f ≫ g) ⁻¹ᵁ O))) ∘
        ⇑(Etale.pullbackUnitApp (f ≫ g) N O) =
      ⇑(Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O)) ∘ ⇑(Etale.pullbackUnitApp g N O) :=
    funext (Etale.pullbackUnitApp_comp f g N O)
  rw [← Function.Bijective.of_comp_iff' hc, e]
  exact Function.Bijective.of_comp_iff' hf _

lemma bijective_pullbackUnitApp_comp_right_iff (g : V ⟶ T) (h : T ⟶ U) [IsOpenImmersion h]
    (N : U.Modules) (O : U.Opens) (hO : O ≤ h.opensRange) :
    Function.Bijective (Etale.pullbackUnitApp (g ≫ h) N O) ↔
      Function.Bijective (Etale.pullbackUnitApp g ((Scheme.Modules.pullback h).obj N) (h ⁻¹ᵁ O)) := by
  have hc := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp g h).inv.app N).app ((g ≫ h) ⁻¹ᵁ O))
  have hh := Etale.pullbackUnitApp_bijective h N hO
  have e : ⇑(ConcreteCategory.hom
      (((Scheme.Modules.pullbackComp g h).inv.app N).app ((g ≫ h) ⁻¹ᵁ O))) ∘
        ⇑(Etale.pullbackUnitApp (g ≫ h) N O) =
      ⇑(Etale.pullbackUnitApp g _ (h ⁻¹ᵁ O)) ∘ ⇑(Etale.pullbackUnitApp h N O) :=
    funext (Etale.pullbackUnitApp_comp g h N O)
  rw [← Function.Bijective.of_comp_iff' hc, e]
  exact Function.Bijective.of_comp_iff _ hh

lemma bijective_pullbackUnitApp_congr (g : T ⟶ U) (N : U.Modules) {O O' : U.Opens} (h : O = O') :
    Function.Bijective (Etale.pullbackUnitApp g N O) ↔
      Function.Bijective (Etale.pullbackUnitApp g N O') := by
  subst h
  rfl

end Move

section Unit

variable {X Y : Scheme.{u}}

theorem bijective_pullbackUnitApp_of_isClosedImmersion (ψ : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) [IsClosedImmersion (ψ ∣_ V)]
    (hkill : ∀ a : Γ(X, V.ι ''ᵁ ⊤), ψ.app (V.ι ''ᵁ ⊤) a = 0 →
      ∀ m : Γ(F, V.ι ''ᵁ ⊤), a • m = 0) :
    Function.Bijective (Etale.pullbackUnitApp ψ F V) := by
  rw [← bijective_pullbackUnitApp_comp_left_iff (ψ ⁻¹ᵁ V).ι ψ F V (by simp),
    ← morphismRestrict_ι ψ V, bijective_pullbackUnitApp_comp_right_iff (ψ ∣_ V) V.ι F V (by simp),
    bijective_pullbackUnitApp_congr _ _ (Scheme.Opens.ι_preimage_self V)]
  have : IsAffine V := hV
  obtain ⟨hT, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (ψ ∣_ V)
  let e := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app F
  have : ((Scheme.Modules.pullback V.ι).obj F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso e inferInstance
  refine bijective_pullbackSection_of_surjective (ψ ∣_ V) _ hsurj fun a ha n => ?_

  have ha' : ψ.app (V.ι ''ᵁ ⊤) a = 0 := by
    rw [morphismRestrict_appTop] at ha
    have hinj := (ConcreteCategory.bijective_of_isIso
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage ψ V ⊤)).op)).1
    exact hinj (by rw [map_zero]; exact ha)
  have key : ∀ n' : Γ(F.restrict V.ι, ⊤), a • n' = 0 := fun n' => by
    have hi := ConcreteCategory.bijective_of_isIso (F.restrictAppIso V.ι ⊤).hom
    apply hi.1
    have hs := congrArg (fun φ : Γ(F.restrict V.ι, ⊤) ⟶ Γ(F, V.ι ''ᵁ ⊤) => φ n')
      (Scheme.Modules.smul_restrictAppIso_hom V.ι F ⊤ a)
    simp only [ConcreteCategory.comp_apply, Scheme.Opens.ι_appIso, Iso.refl_inv] at hs
    change (F.restrictAppIso V.ι ⊤).hom (a • n') = _
    rw [map_zero]
    refine (show _ = _ from hs).trans ?_
    exact hkill a ha' _
  have h1 : n = e.hom.app ⊤ (e.inv.app ⊤ n) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [h1, ← Scheme.Modules.Hom.app_smul, key, map_zero]

theorem bijective_unit_app_of_le (ψ : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] (W : X.Opens)
    [IsClosedImmersion (ψ ∣_ W)]
    (hkill : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → ∀ a : Γ(X, V), ψ.app V a = 0 →
      ∀ m : Γ(F, V), a • m = 0) :
    ∀ V ≤ W, Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction ψ).unit.app F).app V) := by
  refine bijective_app_of_bijective_app_affine _ W fun V hV hVW => ?_
  have hE : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVW
  have hci : IsClosedImmersion (ψ ∣_ V) := by
    have e := morphismRestrictRestrict ψ W (W.ι ⁻¹ᵁ V)
    have h := (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion e).1 inferInstance
    rwa [hE] at h
  have hVtop : V.ι ''ᵁ ⊤ = V := Scheme.Opens.ι_image_top V
  exact bijective_pullbackUnitApp_of_isClosedImmersion ψ F hV fun a ha m =>
    hkill _ (by rw [hVtop]; exact hV) (hVtop.le.trans hVW) a ha m

theorem isIso_counit_of_isClosedImmersion (j : Y ⟶ X) [IsClosedImmersion j] (G : Y.Modules)
    [G.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction j).counit.app G) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction j
  let P := (Scheme.Modules.pushforward j).obj G
  have : P.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom j G
  have : IsClosedImmersion (j ∣_ ⊤) := inferInstance
  have hu : IsIso (adj.unit.app P) := by
    refine isIso_of_bijective_app _ fun V => ?_
    refine bijective_unit_app_of_le j P ⊤ (fun V _ _ a ha m => ?_) V le_top
    change j.app V a • (show Γ(G, j ⁻¹ᵁ V) from m) = 0
    rw [ha, zero_smul]
  have htri := adj.right_triangle_components G
  have hp : IsIso ((Scheme.Modules.pushforward j).map (adj.counit.app G)) := by
    have : (Scheme.Modules.pushforward j).map (adj.counit.app G) = inv (adj.unit.app P) := by
      rw [← cancel_epi (adj.unit.app P), IsIso.hom_inv_id]
      exact htri
    rw [this]
    infer_instance
  refine isIso_of_bijective_app _ fun V => ?_
  obtain ⟨U, rfl⟩ : ∃ U : X.Opens, j ⁻¹ᵁ U = V := by
    obtain ⟨U, hU, hUV⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.1 V.isOpen
    exact ⟨⟨U, hU⟩, Opens.ext hUV⟩
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pushforward j).map (adj.counit.app G)).app U)

end Unit

end

end GroundTheory.Arith.SchemeCoh
