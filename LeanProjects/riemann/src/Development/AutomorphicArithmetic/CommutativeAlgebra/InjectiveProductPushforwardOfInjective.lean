import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory.PwInj

universe u

variable {C : Type u} [Category.{0} C] {S : Type 1} [Ring S]

private noncomputable def lamMap (W : C) (P : Cᵒᵖ ⥤ ModuleCat.{1} S) {T T' : Cᵒᵖ} (h : T ⟶ T') :
    ((T.unop ⟶ W) →₀ P.obj T) →ₗ[S] ((T'.unop ⟶ W) →₀ P.obj T') :=
  Finsupp.lsum ℕ fun g => (Finsupp.lsingle (h.unop ≫ g)).comp (P.map h).hom

private lemma lamMap_single (W : C) (P : Cᵒᵖ ⥤ ModuleCat.{1} S) {T T' : Cᵒᵖ} (h : T ⟶ T')
    (g : T.unop ⟶ W) (m : P.obj T) :
    lamMap W P h (Finsupp.single g m) = Finsupp.single (h.unop ≫ g) ((P.map h).hom m) := by
  simp [lamMap]

private noncomputable def lam (W : C) (P : Cᵒᵖ ⥤ ModuleCat.{1} S) : Cᵒᵖ ⥤ ModuleCat.{1} S where
  obj T := ModuleCat.of S ((T.unop ⟶ W) →₀ P.obj T)
  map h := ModuleCat.ofHom (lamMap W P h)
  map_id T := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    simp [lamMap_single]
  map_comp f h := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    simp [lamMap_single]

private lemma mr_single {A : Type} {M N : Type 1} [AddCommGroup M] [AddCommGroup N] [Module S M]
    [Module S N] (f : M →ₗ[S] N) (a : A) (m : M) :
    Finsupp.mapRange.linearMap f (Finsupp.single a m) = Finsupp.single a (f m) := by
  simp

private lemma pmap_op (P : Cᵒᵖ ⥤ ModuleCat.{1} S) {X Y Y' Z : C}
    (a : Y ⟶ X) (b : Z ⟶ Y) (c : Y' ⟶ X) (d : Z ⟶ Y') (h : b ≫ a = d ≫ c) (m : P.obj (op X)) :
    (P.map b.op).hom ((P.map a.op).hom m) = (P.map d.op).hom ((P.map c.op).hom m) := by
  have e := congrArg (fun f : Z ⟶ X => (P.map f.op).hom m) h
  simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  exact e

private lemma pmap_id (P : Cᵒᵖ ⥤ ModuleCat.{1} S) {X Y : C}
    (a : Y ⟶ X) (b : X ⟶ Y) (h : b ≫ a = 𝟙 X) (m : P.obj (op X)) :
    (P.map b.op).hom ((P.map a.op).hom m) = m := by
  have e := congrArg (fun f : X ⟶ X => (P.map f.op).hom m) h
  simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  simpa using e

private noncomputable def lamF (W : C) : (Cᵒᵖ ⥤ ModuleCat.{1} S) ⥤ (Cᵒᵖ ⥤ ModuleCat.{1} S) where
  obj P := lam W P
  map {P Q} φ :=
    { app := fun T => ModuleCat.ofHom (Finsupp.mapRange.linearMap (φ.app T).hom)
      naturality := fun T T' h => by
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext
        intro g m
        change Finsupp.mapRange.linearMap (φ.app T').hom (lamMap W P h (Finsupp.single g m)) =
          lamMap W Q h (Finsupp.mapRange.linearMap (φ.app T).hom (Finsupp.single g m))
        rw [lamMap_single, mr_single, mr_single, lamMap_single]
        exact congrArg _ (NatTrans.naturality_apply φ h m) }
  map_id P := by
    ext T : 2
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    exact mr_single _ g m
  map_comp {P Q Q'} φ ψ := by
    ext T : 2
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    change Finsupp.mapRange.linearMap ((φ ≫ ψ).app T).hom (Finsupp.single g m) =
      Finsupp.mapRange.linearMap (ψ.app T).hom
        (Finsupp.mapRange.linearMap (φ.app T).hom (Finsupp.single g m))
    rw [mr_single, mr_single, mr_single]
    rfl

private lemma lamF_map_single (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S} (φ : P ⟶ Q) (T : Cᵒᵖ)
    (g : T.unop ⟶ W) (m : P.obj T) :
    (((lamF W).map φ).app T).hom (Finsupp.single g m) = Finsupp.single g ((φ.app T).hom m) :=
  mr_single _ g m

private instance (W : C) : (lamF (S := S) W).PreservesMonomorphisms where
  preserves {P Q} φ _ := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    have h := (NatTrans.mono_iff_mono_app φ).1 inferInstance T
    rw [ModuleCat.mono_iff_injective] at h ⊢
    exact Finsupp.mapRange_injective _ (map_zero _) h

variable [HasBinaryProducts C]

set_option backward.isDefEq.respectTransparency false in

private noncomputable def adjTo (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S} (α : lam W P ⟶ Q) :
    P ⟶ (prod.functor.obj W).op ⋙ Q where
  app T := ModuleCat.ofHom
    ((α.app (op (W ⨯ T.unop))).hom ∘ₗ (Finsupp.lsingle (prod.fst : W ⨯ T.unop ⟶ W)) ∘ₗ
      (P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom)
  naturality T T' h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (α.app (op (W ⨯ T'.unop))).hom (Finsupp.single (prod.fst : W ⨯ T'.unop ⟶ W)
        ((P.map (prod.snd : W ⨯ T'.unop ⟶ T'.unop).op).hom ((P.map h).hom m))) =
      (Q.map ((prod.functor.obj W).map h.unop).op).hom
        ((α.app (op (W ⨯ T.unop))).hom (Finsupp.single (prod.fst : W ⨯ T.unop ⟶ W)
          ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m)))
    have e := NatTrans.naturality_apply α ((prod.functor.obj W).map h.unop).op
      (Finsupp.single (prod.fst : W ⨯ T.unop ⟶ W) ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m))
    refine Eq.trans ?_ e
    refine congrArg _ ?_
    change _ = lamMap W P ((prod.functor.obj W).map h.unop).op (Finsupp.single _ _)
    rw [lamMap_single]
    have e1 : ((prod.functor.obj W).map h.unop).op.unop ≫ (prod.fst : W ⨯ T.unop ⟶ W) = prod.fst := by
      simp
    rw [e1]
    refine congrArg _ ?_
    exact pmap_op P h.unop prod.snd prod.snd ((prod.functor.obj W).map h.unop) (by simp) m

private lemma adjTo_app (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S} (α : lam W P ⟶ Q) (T : Cᵒᵖ) (m : P.obj T) :
    ((adjTo W α).app T).hom m = (α.app (op (W ⨯ T.unop))).hom (Finsupp.single (prod.fst : W ⨯ T.unop ⟶ W)
      ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m)) := rfl

private noncomputable def invApp (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S}
    (u : P ⟶ (prod.functor.obj W).op ⋙ Q) (T : Cᵒᵖ) :
    ((T.unop ⟶ W) →₀ P.obj T) →ₗ[S] Q.obj T :=
  Finsupp.lsum ℕ fun g => (Q.map (prod.lift g (𝟙 T.unop)).op).hom ∘ₗ (u.app T).hom

set_option backward.isDefEq.respectTransparency false in
private lemma invApp_single (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S}
    (u : P ⟶ (prod.functor.obj W).op ⋙ Q) (T : Cᵒᵖ) (g : T.unop ⟶ W) (m : P.obj T) :
    invApp W u T (Finsupp.single g m) = (Q.map (prod.lift g (𝟙 T.unop)).op).hom ((u.app T).hom m) := by
  simp only [invApp, Finsupp.lsum_single, LinearMap.comp_apply]
  try rfl

set_option backward.isDefEq.respectTransparency false in

private noncomputable def adjInv (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S}
    (u : P ⟶ (prod.functor.obj W).op ⋙ Q) : lam W P ⟶ Q where
  app T := ModuleCat.ofHom (invApp W u T)
  naturality T T' h := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    change invApp W u T' (lamMap W P h (Finsupp.single g m)) =
      (Q.map h).hom (invApp W u T (Finsupp.single g m))
    rw [lamMap_single, invApp_single, invApp_single]
    have e : (u.app T').hom ((P.map h).hom m) =
        (Q.map ((prod.functor.obj W).map h.unop).op).hom ((u.app T).hom m) :=
      NatTrans.naturality_apply u h m
    rw [e]
    exact pmap_op Q ((prod.functor.obj W).map h.unop) (prod.lift (h.unop ≫ g) (𝟙 T'.unop))
      (prod.lift g (𝟙 T.unop)) h.unop (by apply Limits.prod.hom_ext <;> simp) _

set_option backward.isDefEq.respectTransparency false in

private noncomputable def lamAdj (W : C) :
    lamF (S := S) W ⊣ (Functor.whiskeringLeft _ _ (ModuleCat.{1} S)).obj (prod.functor.obj W).op :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := adjTo W
          invFun := adjInv W
          left_inv := fun α => by
            ext T : 2
            apply ModuleCat.hom_ext
            apply Finsupp.lhom_ext
            intro g m
            change invApp W (adjTo W α) T (Finsupp.single g m) = (α.app T).hom (Finsupp.single g m)
            rw [invApp_single, adjTo_app]
            have e := NatTrans.naturality_apply α (prod.lift g (𝟙 T.unop)).op
              (Finsupp.single (prod.fst : W ⨯ T.unop ⟶ W) ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m))
            refine e.symm.trans (congrArg _ ?_)
            change lamMap W P (prod.lift g (𝟙 T.unop)).op _ = _
            rw [lamMap_single]
            have e1 : (prod.lift g (𝟙 T.unop)).op.unop ≫ (prod.fst : W ⨯ T.unop ⟶ W) = g := by simp
            rw [e1]
            refine congrArg _ ?_
            exact (pmap_id P (prod.snd : W ⨯ T.unop ⟶ T.unop) (prod.lift g (𝟙 T.unop)) (by simp) m)
          right_inv := fun u => by
            ext T : 2
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro m
            rw [adjTo_app]
            change invApp W u (op (W ⨯ T.unop)) (Finsupp.single _ _) = _
            rw [invApp_single]
            have e : (u.app (op (W ⨯ T.unop))).hom ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m) =
                (Q.map ((prod.functor.obj W).map (prod.snd : W ⨯ T.unop ⟶ T.unop)).op).hom ((u.app T).hom m) :=
              NatTrans.naturality_apply u (prod.snd : W ⨯ T.unop ⟶ T.unop).op m
            refine (congrArg (Q.map (prod.lift (prod.fst : W ⨯ T.unop ⟶ W) (𝟙 (W ⨯ T.unop))).op).hom e).trans ?_
            exact pmap_id Q ((prod.functor.obj W).map (prod.snd : W ⨯ T.unop ⟶ T.unop))
              (prod.lift (prod.fst : W ⨯ T.unop ⟶ W) (𝟙 (W ⨯ T.unop)))
              (by apply Limits.prod.hom_ext <;> simp <;> exact Category.id_comp _) _ }
      homEquiv_naturality_left_symm := fun {P P' Q} f g => by
        ext T : 2
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext
        intro a m
        change invApp W (f ≫ g) T (Finsupp.single a m) =
          invApp W g T ((((lamF W).map f).app T).hom (Finsupp.single a m))
        rw [lamF_map_single, invApp_single, invApp_single]
        rfl
      homEquiv_naturality_right := fun {P Q Q'} f g => rfl }

end UpperTheory.PwInj

open UpperTheory.PwInj in

private noncomputable def UpperTheory.PwInj.sheafAdj (R : Type) [CommRing R] (W : Scheme.{0}) :
    (sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ lamF W ⋙
      presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))) ⊣ pw R W :=
  ((lamAdj W).comp (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))).restrictFullyFaithful
    (iC := sheafToPresheaf _ _) (iD := 𝟭 _)
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ ((prodW W).sheafPushforwardContinuousCompSheafToPresheafIso
      (ModuleCat.{1} (ULift.{1} R)) Scheme.etaleTopology.{0} Scheme.etaleTopology.{0}).symm)

theorem UpperTheory.injective_productPushforward_of_injective :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) (J : Shv R) [Injective J], Injective ((pw R W).obj J) := by
  intro R _ W J _
  exact Injective.injective_of_adjoint (UpperTheory.PwInj.sheafAdj R W) J
