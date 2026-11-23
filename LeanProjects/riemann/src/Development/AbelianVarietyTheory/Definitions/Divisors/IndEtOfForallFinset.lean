import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIndEtaleOfForallFinset

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct

namespace GlobalTheory.EtC

abbrev AbCx : Type 2 := CochainComplex AddCommGrpCat.{1} ℤ

def SurjH {C D : AbCx} (ψ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (z : D.X n), D.d n (n + 1) z = 0 →
    ∃ (c : C.X n) (y : D.X (n - 1)), C.d n (n + 1) c = 0 ∧ ψ.f n c = z + D.d (n - 1) n y

def InjH {C D : AbCx} (ψ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (c : C.X n), C.d n (n + 1) c = 0 → (∃ y : D.X (n - 1), ψ.f n c = D.d (n - 1) n y) →
    ∃ b : C.X (n - 1), C.d (n - 1) n b = c

section Abstract
variable {T : Type 1} [Category.{0} T]

def WExact (M : T ⥤ AddCommGrpCat.{1}) {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) : Prop :=
  Function.Injective (M.map (a.app ⦋0⦌)) ∧
  (∀ y : M.obj (X.obj ⦋0⦌), M.map (X.δ (n := 0) 0) y = M.map (X.δ (n := 0) 1) y → ∃ x : M.obj U, M.map (a.app ⦋0⦌) x = y) ∧
  ∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ M)).ExactAt (n + 1)

abbrev term (C : T ⥤ AbCx) (n : ℤ) : T ⥤ AddCommGrpCat.{1} := C ⋙ HomologicalComplex.eval _ _ n

def LocExact (Cov : MorphismProperty T) (C : T ⥤ AbCx) : Prop :=
  ∀ (n : ℤ) (U : T) (z : (C.obj U).X n), (C.obj U).d n (n + 1) z = 0 →
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (C.obj V).X (n - 1), (C.obj V).d (n - 1) n y = (C.map g).f n z

def LocSurj (Cov : MorphismProperty T) {C D : T ⥤ AbCx} (φ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (U : T) (z : (D.obj U).X n), (D.obj U).d n (n + 1) z = 0 →
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ (c : (C.obj V).X n) (y : (D.obj V).X (n - 1)), (C.obj V).d n (n + 1) c = 0 ∧
      (φ.app V).f n c = (D.map g).f n z + (D.obj V).d (n - 1) n y

def LocInj (Cov : MorphismProperty T) {C D : T ⥤ AbCx} (φ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (U : T) (c : (C.obj U).X n), (C.obj U).d n (n + 1) c = 0 →
    (∃ y : (D.obj U).X (n - 1), (φ.app U).f n c = (D.obj U).d (n - 1) n y) →
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ b : (C.obj V).X (n - 1), (C.obj V).d (n - 1) n b = (C.map g).f n c

def Refines (Cov : MorphismProperty T)
    (Q : ∀ (U : T) (X : CosimplicialObject T), ((CosimplicialObject.const T).obj U ⟶ X) → Prop) : Prop :=
  ∀ (U V : T) (g : U ⟶ V), Cov g → ∃ (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X) (h : V ⟶ X.obj ⦋0⦌),
    g ≫ h = a.app ⦋0⦌ ∧ Q U X a

def lev (Ψ : T ⥤ PShᵒᵖ) {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) :
    ((X ⋙ Ψ).leftOp : Spc) ⟶ disc.obj (Ψ.obj U).unop where
  app n := (Ψ.map (a.app n.unop)).unop
  naturality m n f := by
    have h : a.app n.unop ≫ X.map f.unop = a.app m.unop := (a.naturality f.unop).symm.trans (Category.id_comp _)
    change (Ψ.map (a.app n.unop) ≫ Ψ.map (X.map f.unop)).unop = (Ψ.map (a.app m.unop)).unop ≫ 𝟙 _
    rw [← Ψ.map_comp, h, Category.comp_id]

def coAug [HasFiniteWidePushouts T] {U V : T} (g : U ⟶ V) : (CosimplicialObject.const T).obj U ⟶ (Arrow.mk g).cechConerve :=
  (Arrow.mk g).augmentedCechConerve.hom

end Abstract

variable (R : Type) [CommRing R]

def HCK (I : Cx R) : (Cx R)ᵒᵖ ⥤ AbCx where
  obj K := HomComplex K.unop I
  map f :=
    { f := fun n => AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun β : Cochain _ I n => (Cochain.ofHom f.unop).comp β (zero_add n))
        (fun _ _ => Cochain.comp_add _ _ _ _))
      comm' := fun i j _ => by
        ext β
        exact δ_ofHom_comp f.unop β j }
  map_id K := by
    ext n β
    exact Cochain.id_comp β
  map_comp f g := by
    ext n β
    change (Cochain.ofHom (g.unop ≫ f.unop)).comp β (zero_add n) =
      (Cochain.ofHom g.unop).comp ((Cochain.ofHom f.unop).comp β (zero_add n)) (zero_add n)
    rw [Cochain.ofHom_comp]
    exact Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n)

def HC (F : Shv R) : Spcᵒᵖ ⥤ AbCx := (chains R).op ⋙ HCK R (res R F)

def Hyp {T : Type 1} [Category.{0} T] (Φ : T ⥤ Spcᵒᵖ) {U : T} {X : CosimplicialObject T}
    (a : (CosimplicialObject.const T).obj U ⟶ X) : Prop :=
  ∀ k : SimplexCategoryᵒᵖ, QuasiIso ((chains R).map (lev (Φ ⋙ ((evaluation _ PSh).obj k).op) a))

variable {R} in

def onRings (F : Shv R) : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R) := Scheme.Spec.rightOp ⋙ F.obj

variable {R} in

def Finitary (F : Shv R) : Prop := PreservesFilteredColimitsOfSize.{0, 0} (onRings F)

variable {R} in

abbrev Sec.pull {F : Shv R} {U V : Scheme.{0}} (j : V ⟶ U) (x : Sec F U) : Sec F V := (F.obj.map j.op).hom x

def ContCone (F : Shv R) {I : Type} [SmallCategory I] [IsCofiltered I] {G : I ⥤ Spc} (c : Cone G) : Prop :=
  ∀ n : ℤ, (∀ x : H R c.pt F n, ∃ (i : I) (y : H R (G.obj i) F n), pull R (c.π.app i) F n y = x) ∧
    ∀ (i : I) (y : H R (G.obj i) F n), pull R (c.π.app i) F n y = 0 → ∃ (k : I) (f : k ⟶ i), pull R (G.map f) F n y = 0

def AcycF (E : Spc) (F : Shv R) : Prop := ∀ n : ℤ, 0 < n → Subsingleton (H R E F n)

def EtFF : MorphismProperty CommRingCat.{0} := fun _ _ g => g.hom.Etale ∧ g.hom.FaithfullyFlat

def IndEt (A O : Type) [CommRing A] [CommRing O] [Algebra A O] : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O)

def IndFEt (A O : Type) [CommRing A] [CommRing O] [Algebra A O] : Prop :=
  MorphismProperty.ind.{0} (RingHom.toMorphismProperty fun f => f.Etale ∧ f.Finite) (CommRingCat.ofHom (algebraMap A O))

theorem IndFEt.indEt {A O : Type} [CommRing A] [CommRing O] [Algebra A O] (h : IndFEt A O) : IndEt A O := by
  obtain ⟨J, _, _, D, t, s, hs, hj⟩ := h
  exact ⟨J, inferInstance, inferInstance, D, t, s, hs, fun j => ⟨(hj j).1.1, (hj j).2⟩⟩

theorem indEt_of_etale (A O : Type) [CommRing A] [CommRing O] [Algebra A O] [Algebra.Etale A O] : IndEt A O :=
  MorphismProperty.le_ind _ _ (RingHom.etale_algebraMap.2 inferInstance)

theorem indFEt_of_finite_etale (A O : Type) [CommRing A] [CommRing O] [Algebra A O] [Algebra.Etale A O] [Module.Finite A O] :
    IndFEt A O :=
  MorphismProperty.le_ind _ _ ⟨RingHom.etale_algebraMap.2 inferInstance, RingHom.finite_algebraMap.2 inferInstance⟩

theorem indEt_of_forall_finset (A O : Type) [CommRing A] [CommRing O] [Algebra A O]
    (h : ∀ s : Finset O, ∃ T : Subalgebra A O, Algebra.Etale A T ∧ (s : Set O) ⊆ T) : IndEt A O :=
  GlobalTheory.IndEtaleUnion.isIndEtale_of_forall_finset A O h

def bc {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) : Over S ⥤ Spc where
  obj U := pullback p (sch.map U.hom)
  map {U V} g := pullback.map p (sch.map U.hom) p (sch.map V.hom) (𝟙 _) (sch.map g.left) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← sch.map_comp, Over.w g])
  map_id U := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

def bcMap {E E' : Spc} {S : Scheme.{0}} (α : E ⟶ E') (p : E' ⟶ sch.obj S) : bc (α ≫ p) ⟶ bc p where
  app U := pullback.map (α ≫ p) (sch.map U.hom) p (sch.map U.hom) α (𝟙 _) (𝟙 _) (by simp) (by simp)
  naturality U V g := by apply pullback.hom_ext <;> simp [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

def QcqsOver {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) : Prop :=
  ∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k),
    QuasiCompact r ∧ QuasiSeparated r ∧ e.hom ≫ p.app k = yoneda.map r

def IsStalk {S : Scheme.{0}} (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S) : Prop :=
  SH O ∧ ∃ (A : Type) (_ : CommRing A) (_ : Algebra A O) (j : Spec (CommRingCat.of A) ⟶ S), Etale j ∧ IndEt A O ∧
    s = Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ j

variable {R} in

def Gen (F : Shv R) (S : Scheme.{0}) (g : Sec F S) : Prop :=
  ∀ (U : Scheme.{0}) (s : U ⟶ S),
    (∀ (x : Sec F U) (u : U), ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (c : R), Etale j ∧ j v = u ∧
      Sec.pull j x = (ULift.up c : ULift.{1} R) • Sec.pull (j ≫ s) g) ∧
    ∀ c : R, Nonempty U → (ULift.up c : ULift.{1} R) • Sec.pull s g = 0 → c = 0

variable {R} in

def val {P : PSh} {F : Shv R} (s : (free R).obj P ⟶ F) (U : Scheme.{0}) (x : P.obj (op U)) : Sec F U :=
  (s.hom.app (op U)).hom (freeGen R P U x)

def cechPt {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    Sx (cech f) k U :=
  (WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x) (fun i => yoneda.map (y i))
    (fun i => by rw [← yoneda.map_comp, h i])).app (op U) (𝟙 U)

variable {R} in

def cobd {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ F :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((free R).map (SimplicialObject.δ E i) ≫ s)

variable {R} in

def IsCls {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F n) : Prop :=
  ∃ z : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z = x ∧
    z.1 = Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n

variable {R} in

def Z1 (F : Shv R) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : AddSubgroup ((onRings F).obj (CommRingCat.of (B ⊗[A] B))) :=
  AddMonoidHom.eqLocus
    ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom.toAddMonoidHom
    (((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom.toAddMonoidHom +
     ((onRings F).map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom.toAddMonoidHom)

def UCoc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (u : (B ⊗[A] B)ˣ) : Prop :=
  Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (u : B ⊗[A] B) =
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) (u : B ⊗[A] B) *
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) (u : B ⊗[A] B)

def descMod (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (u : (B ⊗[A] B)ˣ) : Submodule A B :=
  LinearMap.eqLocus ((LinearMap.mulLeft A (u : B ⊗[A] B)) ∘ₗ (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap)
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap

example (A : Type) [CommRing A] : IndFEt A A := indFEt_of_finite_etale A A

example (A : Type) [CommRing A] : IndEt A A := (indFEt_of_finite_etale A A).indEt

example : IndEt ℝ ℂ := GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.isStrictHenselisation_real_complex.2.2.2

def idCone (E : Spc) : Cone (Functor.fromPUnit.{0} E) where
  pt := E
  π := { app := fun _ => 𝟙 E, naturality := fun _ _ _ => by simp }

theorem contCone_idCone (F : Shv R) (E : Spc) : ContCone R F (idCone E) := by
  intro n
  refine ⟨fun x => ⟨⟨⟨⟩⟩, x, pull_id R E F n x⟩, fun i y hy => ⟨i, 𝟙 i, ?_⟩⟩
  rw [CategoryTheory.Functor.map_id]
  exact hy

end GlobalTheory.EtC

end
