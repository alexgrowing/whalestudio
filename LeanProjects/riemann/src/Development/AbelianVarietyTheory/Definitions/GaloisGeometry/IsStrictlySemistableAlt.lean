import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def IsTransfer {Z X : Scheme.{0}} (f : Z ⟶ X) (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : Prop :=
  ∀ (S : Scheme.{0}) (x : S ⟶ X) (m : ℕ) (s : Fin m → (S ⟶ Z)) (hs : ∀ j, s j ≫ f = x),
    IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 S) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => S) ⟶ pullback f x) →
    (freeOn R).map x ≫ t = ∑ j, (freeOn R).map (s j)

def alongS (F : Shv R) (n : ℕ) {Z X : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : HS R F n Z →+ HS R F n X where
  toFun x := (Abelian.Ext.mk₀ t).comp x (zero_add n)
  map_zero' := Abelian.Ext.comp_zero _ _ _ _ _
  map_add' _ _ := Abelian.Ext.comp_add _ _ _ _

def pullS (F : Shv R) (n : ℕ) {X Y : Scheme.{0}} (f : X ⟶ Y) : HS R F n Y →+ HS R F n X := alongS R F n ((freeOn R).map f)

def push (n : ℕ) {Z X : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : H R n Z →ₗ[R] H R n X where
  toFun x := (Abelian.Ext.mk₀ t).comp (x : HS R (coef R) n Z) (zero_add n)
  map_add' _ _ := Abelian.Ext.comp_add _ _ _ _
  map_smul' r _ := Abelian.Ext.comp_smul _ _ _ (ULift.up r : ULift.{1} R)

end Transfer

section Mu

variable (n : ℕ) [NeZero n]

def Mu (A : Type) [CommRing A] : Type := Additive (rootsOfUnity n A)

instance (A : Type) [CommRing A] : AddCommGroup (Mu n A) := inferInstanceAs (AddCommGroup (Additive (rootsOfUnity n A)))

instance (A : Type) [CommRing A] : Module (ZMod n) (Mu n A) :=
  AddCommGroup.zmodModule (fun x => by
    have h : (Additive.toMul (show Additive (rootsOfUnity n A) from x)) ^ n = 1 :=
      Subtype.ext (Additive.toMul (show Additive (rootsOfUnity n A) from x)).2
    exact congrArg Additive.ofMul h)

def Mu.map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : Mu n A →ₗ[ZMod n] Mu n B :=
  AddMonoidHom.toZModLinearMap n
    (MonoidHom.toAdditive (restrictRootsOfUnity φ n) : Additive (rootsOfUnity n A) →+ Additive (rootsOfUnity n B))

omit [NeZero n] in
theorem Mu.ext' {A : Type} [CommRing A] {x y : Mu n A}
    (h : (((Additive.toMul (show Additive (rootsOfUnity n A) from x) : rootsOfUnity n A) : Aˣ) : A) =
      (((Additive.toMul (show Additive (rootsOfUnity n A) from y) : rootsOfUnity n A) : Aˣ) : A)) : x = y :=
  Additive.toMul.injective (Subtype.ext (Units.ext h))

theorem Mu.map_id (A : Type) [CommRing A] : Mu.map n (RingHom.id A) = LinearMap.id :=
  LinearMap.ext fun _ => Mu.ext' n rfl

theorem Mu.map_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    Mu.map n (ψ.comp φ) = (Mu.map n ψ).comp (Mu.map n φ) :=
  LinearMap.ext fun _ => Mu.ext' n rfl

def muPre (i : ℕ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod n)) where
  obj U := ModuleCat.of (ULift.{1} (ZMod n)) (ULift.{1} (⨂[ZMod n] _ : Fin i, Mu n Γ(U.unop, ⊤)))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ⟨PiTensorProduct.map (fun _ => Mu.map n f.unop.appTop.hom) g.down⟩
      map_add' := fun _ _ => congrArg ULift.up (map_add _ _ _)
      map_smul' := fun c _ => congrArg ULift.up (map_smul _ c.down _) }
  map_id U := by
    ext g
    have h : (𝟙 U : U ⟶ U).unop.appTop.hom = RingHom.id _ := by simp
    change PiTensorProduct.map (fun _ => Mu.map n (𝟙 U : U ⟶ U).unop.appTop.hom) g.down = g.down
    rw [h, Mu.map_id, PiTensorProduct.map_id]; rfl
  map_comp {U V W} f g := by
    ext x
    have h : (f ≫ g).unop.appTop.hom = g.unop.appTop.hom.comp f.unop.appTop.hom := by
      rw [unop_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    change PiTensorProduct.map (fun _ => Mu.map n (f ≫ g).unop.appTop.hom) x.down =
      PiTensorProduct.map (fun _ => Mu.map n g.unop.appTop.hom) (PiTensorProduct.map (fun _ => Mu.map n f.unop.appTop.hom) x.down)
    rw [h, Mu.map_comp, PiTensorProduct.map_comp]; rfl

def muSheaf (i : ℕ) : Shv (ZMod n) := (presheafToSheaf _ _).obj (muPre n i)

abbrev HMu (i j : ℕ) (X : Scheme.{0}) : Type 1 := HS (ZMod n) (muSheaf n i) j X

end Mu

def IsStrictlySemistable {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ}) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.Et

end
