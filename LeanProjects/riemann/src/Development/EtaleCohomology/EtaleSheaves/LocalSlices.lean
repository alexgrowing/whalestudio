import Development.EtaleCohomology.EtaleSheaves.LeafLocPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 HomologicalComplex

namespace LateralTheory.E.LocSlicePf

section Gen
variable {C D : Type*} [Category* C] [Category* D]

section Ext
variable [HasZeroMorphisms C] [HasZeroObject C] [HasZeroMorphisms D] [HasZeroObject D]
  (G : C ⥤ D) [G.PreservesZeroMorphisms] {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c) (e : c.Embedding c')

def mX : (o : Option ι) → G.obj (extend.X K o) ≅ extend.X ((G.mapHomologicalComplex c).obj K) o
  | some _ => Iso.refl _
  | none => IsZero.iso (G.map_isZero (extend.isZero_X K rfl)) (extend.isZero_X _ rfl)

def extIso : (G.mapHomologicalComplex c').obj (K.extend e) ≅ ((G.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun i' => mX G K (e.r i')) (by
    intro i' j' _
    change (mX G K (e.r i')).hom ≫ extend.d _ (e.r i') (e.r j') = G.map (extend.d K (e.r i') (e.r j')) ≫ (mX G K (e.r j')).hom
    generalize e.r i' = a
    generalize e.r j' = b
    cases a <;> cases b
    · simp [extend.d]
    · simp [extend.d]
    · simp [extend.d]
    · exact (Category.id_comp _).trans (Category.comp_id _).symm)
end Ext

def hExt [Preadditive C] [HasZeroObject C] {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {K L : HomologicalComplex C c} (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsRelIff] :
    HomotopyEquiv (K.extend e) (L.extend e) where
  hom := extendMap h.hom e
  inv := extendMap h.inv e
  homotopyHomInvId := by simpa [← extendMap_comp, extendMap_id] using h.homotopyHomInvId.extend e
  homotopyInvHomId := by simpa [← extendMap_comp, extendMap_id] using h.homotopyInvHomId.extend e

section Ab
variable [Abelian C] [Abelian D]

def hEq {X Y : D} (e : X ≅ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y) :
    HomotopyEquiv I.cocomplex J.cocomplex where
  hom := InjectiveResolution.desc e.hom J I
  inv := InjectiveResolution.desc e.inv I J
  homotopyHomInvId := (InjectiveResolution.descCompHomotopy e.hom e.inv I J I).symm.trans (by
    simpa using InjectiveResolution.descIdHomotopy _ I)
  homotopyInvHomId := (InjectiveResolution.descCompHomotopy e.inv e.hom J I J).symm.trans (by
    simpa using InjectiveResolution.descIdHomotopy _ J)

def mapInj (P : C ⥤ D) [P.Additive] [P.PreservesInjectiveObjects] [P.PreservesHomology] {Z : C}
    (I : InjectiveResolution Z) : InjectiveResolution (P.obj Z) where
  cocomplex := (P.mapHomologicalComplex _).obj I.cocomplex
  injective n := P.injective_obj_of_injective (I.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex P _ _).inv.app _ ≫ (P.mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

theorem gen (P : C ⥤ D) [P.Additive] [P.PreservesInjectiveObjects] [P.PreservesHomology]
    {A : Type*} [Category* A] [Abelian A] (E : D ⥤ A) [E.Additive] {F G : C}
    (I : InjectiveResolution F) (J : InjectiveResolution G) (e : P.obj F ≅ P.obj G) (n : ℤ) :
    Nonempty ((((P ⋙ E).mapHomologicalComplex _).obj I.cochainComplex).homology n ≅
      (((P ⋙ E).mapHomologicalComplex _).obj J.cochainComplex).homology n) := by
  let h1 := hEq e (mapInj P I) (mapInj P J)
  let h2 := hExt h1 ComplexShape.embeddingUpNat
  let h3 := (HomotopyEquiv.ofIso (extIso P I.cocomplex ComplexShape.embeddingUpNat)).trans
    (h2.trans (HomotopyEquiv.ofIso (extIso P J.cocomplex ComplexShape.embeddingUpNat).symm))
  exact ⟨(E.mapHomotopyEquiv h3).toHomologyIso n⟩
end Ab
end Gen

variable (R : Type) [CommRing R] (X : Scheme.{0})

instance : HasSheafify (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} (Over X) := inferInstance
  infer_instance

instance : (Scheme.etaleTopology.{0}.overPullback (ModuleCat.{1} (ULift.{1} R)) X).Additive where
  map_add := rfl

instance : PreservesFiniteColimits (Scheme.etaleTopology.{0}.overPullback (ModuleCat.{1} (ULift.{1} R)) X) := by
  have := ((Over.forget X).sheafAdjunctionCocontinuous (ModuleCat.{1} (ULift.{1} R))
    (Scheme.etaleTopology.{0}.over X) Scheme.etaleTopology.{0}).leftAdjoint_preservesColimits
  infer_instance

def InjOver : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}),
  (Scheme.etaleTopology.{0}.overPullback (ModuleCat.{1} (ULift.{1} R)) X).PreservesInjectiveObjects

theorem LocSlice_of (hI : InjOver) : LateralTheory.E.LeafLocPf.LocSlice := by
  intro _ R _ X F G ⟨e⟩ n
  have := hI R X
  obtain ⟨i⟩ := gen (Scheme.etaleTopology.{0}.overPullback (ModuleCat.{1} (ULift.{1} R)) X)
    (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (Over.mk (𝟙 X))))
    (injectiveResolution F) (injectiveResolution G) e n
  exact ⟨i.toLinearEquiv.toAddEquiv⟩

end LateralTheory.E.LocSlicePf
