import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenDisjointImageOfIsConstructible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory.GenericConnected

theorem exists_spread {X Y S : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [Algebra R A] (j : Spec (.of R) ⟶ S) {p : X ⟶ S} [QuasiCompact p]
    [LocallyOfFiniteType p] {g : Y ⟶ X} {q : Y ⟶ Spec (.of A)}
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ j))
    (U V : Y.Opens) (hsup : U ⊔ V = ⊤) (hinf : U ⊓ V = ⊥) :
    ∃ (T : Scheme.{0}) (a : T ⟶ Spec (.of R)) (_ : LocallyOfFiniteType a) (_ : IsAffine T)
      (b : Spec (.of A) ⟶ T) (π : Y ⟶ pullback p (a ≫ j)) (U' V' : (pullback p (a ≫ j)).Opens),
      b ≫ a = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      π ≫ pullback.snd p (a ≫ j) = q ≫ b ∧
      U' ⊔ V' = ⊤ ∧ U' ⊓ V' = ⊥ ∧ π ⁻¹ᵁ U' = U ∧ π ⁻¹ᵁ V' = V := by
  classical
  let F : Finset A ⥤ CommRingCat.{0} :=
    { obj s := .of (Algebra.adjoin R (s : Set A))
      map {s t} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cF : Cocone F :=
    { pt := .of A
      «ι» := { app s := CommRingCat.ofHom (Algebra.adjoin R (s : Set A)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcF : IsColimit cF := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : A := x
        exact ⟨({x'} : Finset A), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin R (({x'} : Finset A) : Set A)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset A)ᵒᵖ ⥤ Scheme.{0} := F.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cF.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcF.op
  let a (s : (Finset A)ᵒᵖ) : G.obj s ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R (s.unop : Set A))))
  have ha {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : G.map f ≫ a t = a s := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have ha' (s : (Finset A)ᵒᵖ) :
      cG.π.app s ≫ a s = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let e (s : (Finset A)ᵒᵖ) : G.obj s ⟶ S := a s ≫ j
  have hι {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : G.map f ≫ e t = e s := by
    change G.map f ≫ a t ≫ j = a s ≫ j
    rw [← Category.assoc, ha]
  have hι' (s : (Finset A)ᵒᵖ) :
      cG.π.app s ≫ e s = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ j := by
    change cG.π.app s ≫ a s ≫ j = _
    rw [← Category.assoc, ha']
  let D : (Finset A)ᵒᵖ ⥤ Scheme.{0} :=
    { obj s := pullback p (e s)
      map {s t} f := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ G.map f)
        (by rw [Category.assoc, hι, pullback.condition])
      map_id s := by apply pullback.hom_ext <;> simp
      map_comp f f' := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
            G.map_comp, Category.assoc] }
  let α : D ⟶ G :=
    { app s := pullback.snd p (e s)
      naturality s t f := pullback.lift_snd _ _ _ }
  let π (s : (Finset A)ᵒᵖ) : Y ⟶ pullback p (e s) :=
    pullback.lift g (q ≫ cG.π.app s) (by rw [Category.assoc, hι', H.w])
  let cD : Cone D :=
    { pt := Y
      π :=
        { app := π
          naturality s t f := by
            change 𝟙 Y ≫ π t = π s ≫ pullback.lift _ _ _
            apply pullback.hom_ext
            · rw [Category.id_comp, Category.assoc, pullback.lift_fst, pullback.lift_fst,
                pullback.lift_fst]
            · rw [Category.id_comp, Category.assoc, pullback.lift_snd, pullback.lift_snd,
                pullback.lift_snd_assoc, Category.assoc, cG.w f] } }
  have hπ (s : (Finset A)ᵒᵖ) : IsPullback (π s) q (pullback.snd p (e s)) (cG.π.app s) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (e s)) (v₁₃ := p) (h₂₂ := e s) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [hι', pullback.lift_fst]
    exact H
  have hcD : IsLimit cD := isLimitOfIsPullbackOfIsConnected α cD cG
    { hom := q, w s := (pullback.lift_snd _ _ _).symm } hπ hcG
  have hG (s : (Finset A)ᵒᵖ) : IsAffine (G.obj s) := inferInstanceAs (IsAffine (Spec _))
  have {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (D.map f) := by
    have : IsPullback (D.map f) (pullback.snd p (e s)) (pullback.snd p (e t)) (G.map f) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst p (e t)) (v₁₃ := p) (h₂₂ := e t) ?_
        (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
      rw [hι, pullback.lift_fst]
      exact .of_hasPullback _ _
    exact MorphismProperty.of_isPullback this.flip inferInstance
  have hcpt (s : (Finset A)ᵒᵖ) : CompactSpace (D.obj s) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p (e s))
  have hft (s : (Finset A)ᵒᵖ) : LocallyOfFiniteType (a s) := by
    have : Algebra.FiniteType R (Algebra.adjoin R (s.unop : Set A)) :=
      Algebra.FiniteType.adjoin_of_finite s.unop.finite_toSet
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr this)
  have hnoeth (s : (Finset A)ᵒᵖ) : TopologicalSpace.NoetherianSpace (D.obj s) := by
    have : IsLocallyNoetherian (D.obj s) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p (e s) ≫ a s)
    have : IsNoetherian (D.obj s) := {}
    infer_instance
  have hw {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) (W : (D.obj t).Opens) :
      cD.π.app s ⁻¹ᵁ D.map f ⁻¹ᵁ W = cD.π.app t ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, cD.w]
  have : QuasiCompact q := MorphismProperty.of_isPullback H inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have hsup' : (U : Set Y) ∪ V = Set.univ := by simpa using congr(($hsup : Set Y))
  have hinf' : (U : Set Y) ∩ V = ∅ := by simpa using congr(($hinf : Set Y))
  have hUV : IsCompl (U : Set Y) V := ⟨Set.disjoint_iff_inter_eq_empty.2 hinf', codisjoint_iff.2 hsup'⟩
  have hUc : IsCompact (U : Set Y) := by
    rw [hUV.eq_compl]; exact V.2.isClosed_compl.isCompact
  have hVc : IsCompact (V : Set Y) := by
    rw [hUV.symm.eq_compl]; exact U.2.isClosed_compl.isCompact
  obtain ⟨i₁, U₁, -, hU₁⟩ := exists_preimage_eq D cD hcD U hUc
  obtain ⟨i₂, V₁, -, hV₁⟩ := exists_preimage_eq D cD hcD V hVc
  let f₁ := IsCofiltered.minToLeft i₁ i₂
  let f₂ := IsCofiltered.minToRight i₁ i₂
  obtain ⟨i₃, f₃, h₃⟩ := exists_map_eq_top D cD hcD (D.map f₁ ⁻¹ᵁ U₁ ⊔ D.map f₂ ⁻¹ᵁ V₁) (by
    rw [Scheme.Hom.preimage_sup, hw, hw, hU₁, hV₁]; exact hsup)
  obtain ⟨i₄, f₄, h₄⟩ := exists_map_preimage_le_map_preimage D cD hcD
    (U := D.map f₃ ⁻¹ᵁ D.map f₁ ⁻¹ᵁ U₁ ⊓ D.map f₃ ⁻¹ᵁ D.map f₂ ⁻¹ᵁ V₁) (V := ⊥)
    (TopologicalSpace.NoetherianSpace.isCompact _) (by
    rw [Scheme.Hom.preimage_inf, hw, hw, hw, hw, hU₁, hV₁]; exact hinf.le.trans bot_le)
  refine ⟨G.obj i₄, a i₄, hft _, hG _, cG.π.app i₄, π i₄,
    D.map f₄ ⁻¹ᵁ D.map f₃ ⁻¹ᵁ D.map f₁ ⁻¹ᵁ U₁, D.map f₄ ⁻¹ᵁ D.map f₃ ⁻¹ᵁ D.map f₂ ⁻¹ᵁ V₁,
    ha' _, (hπ _).w, ?_, ?_, ?_, ?_⟩
  · have := congr(D.map f₄ ⁻¹ᵁ $h₃)
    rw [Scheme.Hom.preimage_sup, Scheme.Hom.preimage_sup] at this
    exact this
  · rw [Scheme.Hom.preimage_inf] at h₄
    exact le_bot_iff.1 h₄
  · exact ((hw f₄ _).trans ((hw f₃ _).trans (hw f₁ U₁))).trans hU₁
  · exact ((hw f₄ _).trans ((hw f₃ _).trans (hw f₂ V₁))).trans hV₁

theorem exists_mem_of_genericPoint_mem {T S : Scheme.{0}} [IsIntegral S] [IsNoetherian S]
    (t : T ⟶ S) [LocallyOfFiniteType t] [QuasiCompact t] {C : Set T} {Sg : Set S}
    (hC : Topology.IsConstructible C) (hSg : Dense Sg) (h : genericPoint S ∈ t '' C) :
    ∃ y ∈ C, t y ∈ Sg := by
  by_contra! H
  obtain ⟨V, hV, -, hd⟩ :=
    exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense T S t C Sg hC hSg
      (Set.disjoint_left.2 (by rintro _ ⟨y, hy, rfl⟩; exact H y hy))
  exact Set.disjoint_left.1 hd h
    (((genericPoint_spec S).mem_open_set_iff V.isOpen).mpr (by simpa using hV))

theorem not_mem_image_inter {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T)
    (h : GeometricallyConnected (f.fiberToSpecResidueField (t y)))
    (U V : (pullback f t).Opens) (hsup : U ⊔ V = ⊤) (hinf : U ⊓ V = ⊥) :
    y ∉ (pullback.snd f t '' U) ∩ (pullback.snd f t '' V) := by
  rintro ⟨⟨u, hu, hu'⟩, v, hv, hv'⟩
  have : ConnectedSpace ((pullback.snd f t).fiber y) :=
    h.geometrically_connectedSpace _ _ _
      (isPullback_fiberToSpecResidueField_of_isPullback (.of_hasPullback f t) y)
  have hc : _root_.IsPreconnected (pullback.snd f t ⁻¹' {y}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact isPreconnected_univ.image _ (Scheme.Hom.fiberι _ _).continuous.continuousOn
  have hsup' : (U : Set ↥(pullback f t)) ∪ V = Set.univ := by
    simpa using congr(($hsup : Set ↥(pullback f t)))
  have hinf' : (U : Set ↥(pullback f t)) ∩ V = ∅ := by
    simpa using congr(($hinf : Set ↥(pullback f t)))
  obtain ⟨z, -, hz⟩ := hc U V U.2 V.2 (hsup' ▸ Set.subset_univ _) ⟨u, hu', hu⟩ ⟨v, hv', hv⟩
  rw [hinf'] at hz
  exact hz

end GlobalTheory.GenericConnected

namespace GlobalTheory

open GenericConnected in

theorem geometricallyConnected_genericFibre_of_dense :
    ∀ (X S : Scheme.{0}) [IsIntegral S] [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (Sg : Set S), Dense Sg → (∀ x ∈ Sg, GeometricallyConnected (f.fiberToSpecResidueField x)) → GeometricallyConnected (f.fiberToSpecResidueField (genericPoint S)) := by
  intro X S _ _ f _ _ Sg hSg hc
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have H : IsPullback (fst ≫ f.fiberι _) snd f (y ≫ S.fromSpecResidueField (genericPoint S)) :=
    h.paste_horiz (.of_hasPullback f (S.fromSpecResidueField (genericPoint S)))
  have hy (z : Spec (.of K)) : (y ≫ S.fromSpecResidueField (genericPoint S)) z = genericPoint S := by
    rw [Scheme.Hom.comp_apply]
    exact (S.range_fromSpecResidueField _).le ⟨_, rfl⟩
  generalize y ≫ S.fromSpecResidueField (genericPoint S) = k at H hy
  generalize fst ≫ f.fiberι _ = g at H
  have hne : Nonempty Z := by
    have h1 : genericPoint S ∈ f '' Set.univ := by
      by_contra h0
      obtain ⟨x, hx, hx'⟩ := exists_mem_of_genericPoint_mem (𝟙 S) (C := (f '' Set.univ)ᶜ)
        (f.isConstructible_image .univ).compl hSg ⟨_, h0, rfl⟩
      have := hc x hx'
      have : ConnectedSpace (f.fiber x) :=
        GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField x)
      obtain ⟨w⟩ : Nonempty (f.fiber x) := inferInstance
      exact hx ⟨_, trivial, (f.range_fiberι x).le ⟨w, rfl⟩⟩
    obtain ⟨x, -, hx⟩ := h1
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback H x (default : PrimeSpectrum K)
      (hx.trans (hy _).symm)
    exact ⟨z⟩
  suffices PreconnectedSpace Z from ⟨hne⟩
  refine ⟨fun U V hU hV hUV ⟨u, _, hu⟩ ⟨v, _, hv⟩ ↦ ?_⟩
  by_contra hemp
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hηW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint S)) isOpen_univ
  have : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hr : Set.range k ⊆ Set.range hW.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hW.range_fromSpec, hy]
    exact hηW
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec k hr)
  have hk : Spec.map φ ≫ hW.fromSpec = k := by rw [hφ, IsOpenImmersion.lift_fac]
  algebraize [φ.hom]
  obtain ⟨T, a, _, _, b, π, U', V', hb, hπ, hsup, hinf, hU', hV'⟩ :=
    exists_spread (R := Γ(S, W)) (A := K) hW.fromSpec (p := f) (g := g) (q := snd) (by
      rw [← hk] at H; exact H) ⟨U, hU⟩ ⟨V, hV⟩
      (by ext; simpa using hUV trivial)
      (by ext z; simpa using fun h1 h2 ↦ hemp ⟨z, trivial, h1, h2⟩)
  let t : T ⟶ S := a ≫ hW.fromSpec
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsNoetherian T := {}
  have : QuasiCompact t := inferInstance
  have : IsLocallyNoetherian (pullback f t) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f t)
  have : CompactSpace ↥(pullback f t) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f t)
  have : IsNoetherian (pullback f t) := {}
  have hcons (O : (pullback f t).Opens) :
      Topology.IsConstructible (pullback.snd f t '' O) :=
    (pullback.snd f t).isConstructible_image
      (IsRetrocompact.isConstructible O.2 fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _)
  have hmem (O : (pullback f t).Opens) (z : Z) (hz : z ∈ π ⁻¹ᵁ O) :
      b (default : PrimeSpectrum K) ∈ pullback.snd f t '' O := by
    refine ⟨π z, hz, ?_⟩
    rw [← Scheme.Hom.comp_apply, hπ, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim (α := PrimeSpectrum K) _ _
  obtain ⟨x, hx, hx'⟩ := exists_mem_of_genericPoint_mem t ((hcons U').inter (hcons V')) hSg
    ⟨b (default : PrimeSpectrum K), ⟨hmem U' u (hU' ▸ hu), hmem V' v (hV' ▸ hv)⟩, by
      have hbt : b ≫ t = k := by rw [← Category.assoc, hb]; exact hk
      exact (Scheme.Hom.comp_apply b t _).symm.trans ((congr($hbt _)).trans (hy _))⟩
  exact not_mem_image_inter f t x (hc _ hx') U' V' hsup hinf hx

end GlobalTheory
