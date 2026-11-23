import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {K L M : CochainComplex C ℤ} {m n k : ℤ}

def zcomp (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) : Cocycle K M k :=
  Cocycle.mk (a.1.comp b.1 h) (k + 1) rfl (by
    rw [δ_comp _ _ h (m + 1) (n + 1) (k + 1) rfl rfl rfl]
    simp)

def cpre (a : Cocycle K L m) (M : CochainComplex C ℤ) (n k : ℤ) (h : m + n = k) :
    CohomologyClass L M n →+ CohomologyClass K M k :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun b => CohomologyClass.mk (zcomp a b h)) (fun b b' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact Cocycle.ext (Cochain.comp_add _ _ _ h)))
    (by
      rintro ⟨b, hb⟩ ⟨n', hn', β, rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + n', by omega, a.1.comp β rfl, ?_⟩
      rw [δ_comp _ _ rfl (m + 1) n k (by omega) rfl hn']
      simp [zcomp])

def cpost (K : CochainComplex C ℤ) (b : Cocycle L M n) (m k : ℤ) (h : m + n = k) :
    CohomologyClass K L m →+ CohomologyClass K M k :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun a => CohomologyClass.mk (zcomp a b h)) (fun a a' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact Cocycle.ext (Cochain.add_comp _ _ _ h)))
    (by
      rintro ⟨a, ha⟩ ⟨m', hm', α, rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m' + n, by omega, n.negOnePow • α.comp b.1 rfl, ?_⟩
      rw [δ_units_smul, δ_comp _ _ rfl m (n + 1) k (by omega) hm' rfl]
      simp [zcomp, smul_smul])

theorem cpre_mk (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) :
    cpre a M n k h (CohomologyClass.mk b) = CohomologyClass.mk (zcomp a b h) := rfl

theorem cpost_mk (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) :
    cpost K b m k h (CohomologyClass.mk a) = CohomologyClass.mk (zcomp a b h) := rfl

variable {S : Type*} [Ring S] [Linear S C]

def csmul (K L : CochainComplex C ℤ) (n : ℤ) (r : S) : CohomologyClass K L n →+ CohomologyClass K L n :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun a => CohomologyClass.mk (r • a)) (fun a a' => by rw [smul_add, CohomologyClass.mk_add]))
    (by
      rintro ⟨a, ha⟩ ⟨m', hm', α, rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      exact ⟨m', hm', r • α, δ_smul _ _ _ _⟩)

abbrev cmodule (S : Type*) [Ring S] [Linear S C] (K L : CochainComplex C ℤ) (n : ℤ) : Module S (CohomologyClass K L n) where
  smul r x := csmul K L n r x
  one_smul x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (one_smul _ x)
  mul_smul r s x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (mul_smul r s x)
  smul_zero r := map_zero (csmul K L n r)
  smul_add r := map_add (csmul K L n r)
  add_smul r s x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (add_smul r s x)
  zero_smul x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (zero_smul _ x)

end General

abbrev Shv (R : Type) [CommRing R] : Type 2 := Sheaf (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))

variable (R : Type) [CommRing R]

instance : HasSheafify (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

instance : IsGrothendieckAbelian.{1} (Shv R) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} R))

abbrev PSh : Type 1 := Scheme.{0}ᵒᵖ ⥤ Type

abbrev Spc : Type 1 := SimplicialObject PSh

abbrev Cx : Type 2 := CochainComplex (Shv R) ℤ

def freeP : PSh ⥤ (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :=
  (Functor.whiskeringRight _ _ _).obj (uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R))

def free : PSh ⥤ Shv R := freeP R ⋙ presheafToSheaf _ _

def chainsN : Spc ⥤ ChainComplex (Shv R) ℕ :=
  (SimplicialObject.whiskering _ _).obj (free R) ⋙ AlgebraicTopology.alternatingFaceMapComplex (Shv R)

def chains : Spc ⥤ Cx R := chainsN R ⋙ ComplexShape.embeddingDownNat.extendFunctor (Shv R)

def res (F : Shv R) : Cx R := (injectiveResolution F).cochainComplex

def resι (F : Shv R) : F ⟶ (res R F).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0

def resMap {F G : Shv R} (φ : F ⟶ G) : res R F ⟶ res R G :=
  HomologicalComplex.extendMap (InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F))
    ComplexShape.embeddingUpNat

abbrev HK (K : Cx R) (F : Shv R) (n : ℤ) : Type 1 := CohomologyClass K (res R F) n

instance (priority := low) (K L : Cx R) (n : ℤ) : Module R (CohomologyClass K L n) :=
  letI := cmodule (ULift.{1} R) K L n
  Module.compHom _ (ULift.ringEquiv.symm : R ≃+* ULift.{1} R).toRingHom

abbrev H (E : Spc) (F : Shv R) (n : ℤ) : Type 1 := HK R ((chains R).obj E) F n

abbrev disc : PSh ⥤ Spc := SimplicialObject.const _

def sch : Scheme.{0} ⥤ Spc := yoneda ⋙ disc

abbrev sp (A : Type) [CommRing A] : Spc := sch.obj (Spec (CommRingCat.of A))

abbrev spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : sp B ⟶ sp A := sch.map (Spec.map (CommRingCat.ofHom f))

def HK.pre {K L : Cx R} {m : ℤ} (z : Cocycle K L m) (F : Shv R) (n k : ℤ) (h : m + n = k) : HK R L F n →+ HK R K F k :=
  cpre z (res R F) n k h

def HK.pull {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) : HK R L F n →+ HK R K F n :=
  HK.pre R (Cocycle.ofHom f) F n n (zero_add n)

def HK.ext (K : Cx R) {F G : Shv R} {n : ℤ} (z : Cocycle (res R F) (res R G) n) (m k : ℤ) (h : m + n = k) :
    HK R K F m →+ HK R K G k := cpost K z m k h

def HK.post (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) : HK R K F n →+ HK R K G n :=
  HK.ext R K (Cocycle.ofHom (resMap R φ)) n n (add_zero n)

def pull {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) : H R E' F n →+ H R E F n := HK.pull R ((chains R).map f) F n

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in
theorem _root_.GlobalTheory.EtC.pull_id (E : _root_.GlobalTheory.EtC.Spc)
    (F : _root_.GlobalTheory.EtC.Shv R) (n : ℤ) (x : _root_.GlobalTheory.EtC.H R E F n) :
    _root_.GlobalTheory.EtC.pull R (𝟙 E) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [_root_.GlobalTheory.EtC.pull, _root_.GlobalTheory.EtC.HK.pull,
    _root_.GlobalTheory.EtC.HK.pre,
    _root_.GlobalTheory.EtC.cpre_mk, Functor.map_id]
  congr 1
  ext : 1
  simp [_root_.GlobalTheory.EtC.zcomp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in
theorem _root_.GlobalTheory.EtC.pull_comp {E E' E'' : _root_.GlobalTheory.EtC.Spc} (f : E ⟶ E')
    (g : E' ⟶ E'') (F : _root_.GlobalTheory.EtC.Shv R) (n : ℤ) (x : _root_.GlobalTheory.EtC.H R E'' F n) :
    _root_.GlobalTheory.EtC.pull R (f ≫ g) F n x =
      _root_.GlobalTheory.EtC.pull R f F n (_root_.GlobalTheory.EtC.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [_root_.GlobalTheory.EtC.pull, _root_.GlobalTheory.EtC.HK.pull,
    _root_.GlobalTheory.EtC.HK.pre,
    _root_.GlobalTheory.EtC.cpre_mk, Functor.map_comp]
  congr 1
  ext : 1
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.ofHom_comp]

def pullL {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) : H R E' F n →ₗ[R] H R E F n where
  toFun := pull R f F n
  map_add' := map_add _
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_smul _ _ _ (zero_add n)))

def Eqv {E E' : Spc} (f : E ⟶ E') (F : Shv R) : Prop := ∀ n, Function.Bijective (pull R f F n)

abbrev Sx (E : Spc) (p : ℕ) (U : Scheme.{0}) : Type := (E.obj (op (SimplexCategory.mk p))).obj (op U)

abbrev Sec {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) : Type 1 := F.obj.obj (op U)

def freeGen (P : PSh) (U : Scheme.{0}) (x : P.obj (op U)) : Sec ((free R).obj P) U :=
  ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U)).hom (ModuleCat.freeMk (ULift.up x))

def chainsXIso (E : Spc) (p : ℕ) : ((chains R).obj E).X (-(p : ℤ)) ≅ (free R).obj (E.obj (op (SimplexCategory.mk p))) :=
  ((chainsN R).obj E).extendXIso ComplexShape.embeddingDownNat (i := p) rfl

variable {R} in

def ev {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : Sec (I.X s) U :=
  ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U))).hom (freeGen R _ U x)

def ofRings (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) : Shv R := (presheafToSheaf _ _).obj (Scheme.Γ ⋙ M)

variable {R} in

def ofRings.sec (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) (x : M.obj Γ(U, ⊤)) : Sec (ofRings R M) U :=
  ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U)).hom x

def const (M : Type) [AddCommGroup M] [Module R M] : Shv R :=
  ofRings R ((Functor.const _).obj (ModuleCat.of (ULift.{1} R) (ULift.{1} M)))

abbrev coef : Shv R := const R R

def unitsF : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} ℤ) where
  obj A := ModuleCat.of (ULift.{1} ℤ) (ULift.{1} (Additive Aˣ))
  map f := ModuleCat.ofHom
    { toFun := fun g => ⟨MonoidHom.toAdditive (Units.map f.hom.toMonoidHom) g.down⟩
      map_add' := fun _ _ => congrArg ULift.up (map_add _ _ _)
      map_smul' := fun c _ => congrArg ULift.up (map_zsmul _ c.down _) }
  map_id _ := rfl
  map_comp _ _ := rfl

def Gm : Shv ℤ := ofRings ℤ unitsF

def muSheaf (n : ℕ) [NeZero n] (i : ℕ) : Shv (ZMod n) := (presheafToSheaf _ _).obj (GlobalTheory.Et.muPre n i)

variable {R} in

def restr {S : Type} [CommRing S] (φ : R →+* S) : Shv S ⥤ Shv R :=
  sheafCompose _ (ModuleCat.restrictScalars.{1}
    ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)))

def ofCat (C : CommRingCat.{0} ⥤ Cat.{0,0}) : Spc := (Scheme.Γ ⋙ C ⋙ nerveFunctor).flip

def cst (C : Type) [SmallCategory C] : Spc := ofCat ((Functor.const _).obj (Cat.of C))

def glCat (N : ℕ) : CommRingCat.{0} ⥤ Cat.{0,0} where
  obj A := Cat.of (SingleObj (GL (Fin N) A))
  map f := (SingleObj.mapHom _ _ (Matrix.GeneralLinearGroup.map f.hom)).toCatHom
  map_id A := by
    have : Matrix.GeneralLinearGroup.map (n := Fin N) (𝟙 A : A ⟶ A).hom = MonoidHom.id _ := by ext; rfl
    rw [this]; rfl
  map_comp {A B D} f g := by
    have : Matrix.GeneralLinearGroup.map (n := Fin N) (f ≫ g).hom =
        (Matrix.GeneralLinearGroup.map g.hom).comp (Matrix.GeneralLinearGroup.map f.hom) := by ext; rfl
    rw [this]; rfl

def glMat {N : ℕ} {U : Scheme.{0}} (y : Sx (ofCat (glCat N)) 1 U) : GL (Fin N) Γ(U, ⊤) :=
  (show ComposableArrows (SingleObj (GL (Fin N) Γ(U, ⊤))) 1 from y).hom

def Inv (q : ℕ) (E : Spc) : Prop := ∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → IsUnit (q : Γ(U, ⊤))

def Cover2 {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : Prop := Mono f ∧ Mono g ∧
  ∀ n, Epi (biprod.desc ((free R).map (f.app n)) ((free R).map (g.app n)))

def cech {Y X : Scheme.{0}} (f : Y ⟶ X) : Spc := (Arrow.mk (yoneda.map f)).cechNerve

def cechAug {Y X : Scheme.{0}} (f : Y ⟶ X) : cech f ⟶ sch.obj X := (Arrow.mk (yoneda.map f)).augmentedCechNerve.hom

abbrev Hrel {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) : Type 1 := HK R (mappingCone ((chains R).map f)) F n

def SH (A : Type) [CommRing A] : Prop := ∃ _ : HenselianLocalRing A, IsSepClosed (IsLocalRing.ResidueField A)

def AIC (A : Type) [CommRing A] : Prop := ∀ p : Polynomial A, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0

section Galois
open GlobalTheory.Et
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) in
theorem _root_.GlobalTheory.EtC.galMap_one :
    _root_.GlobalTheory.Et.galMap Ω p 1 = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · simp [_root_.GlobalTheory.Et.galMap_fst]
  · rw [_root_.GlobalTheory.Et.galMap_snd, Category.id_comp]
    convert Category.comp_id _
    convert Spec.map_id _
    rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) in
theorem _root_.GlobalTheory.EtC.galMap_mul (σ τ : Ω ≃ₐ[k] Ω) :
    _root_.GlobalTheory.Et.galMap Ω p (σ * τ) =
      _root_.GlobalTheory.Et.galMap Ω p σ ≫ _root_.GlobalTheory.Et.galMap Ω p τ := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, _root_.GlobalTheory.Et.galMap_fst]
  · simp only [Category.assoc, _root_.GlobalTheory.Et.galMap_snd,
      _root_.GlobalTheory.Et.galMap_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

def gal (F : Shv R) (n : ℤ) : Representation R (Ω ≃ₐ[k] Ω) (H R (sch.obj (geom Ω p)) F n) where
  toFun σ := pullL R (sch.map (galMap Ω p σ)) F n
  map_one' := by
    ext x
    change pull R (sch.map (galMap Ω p 1)) F n x = x
    rw [galMap_one, CategoryTheory.Functor.map_id, pull_id]
  map_mul' σ τ := by
    ext x
    change pull R (sch.map (galMap Ω p (σ * τ))) F n x = pull R _ F n (pull R _ F n x)
    rw [galMap_mul, Functor.map_comp, pull_comp]

end Galois

end GlobalTheory.EtC

end
