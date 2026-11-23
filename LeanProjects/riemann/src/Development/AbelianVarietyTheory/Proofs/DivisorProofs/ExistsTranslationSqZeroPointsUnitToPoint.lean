import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

abbrev ovT (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : Over (Sp R) :=
  Over.mk (spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)))

abbrev ovB (R : Type) [CommRing R] (B : Type) [CommRing B] [Algebra R B] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R B))

theorem one_left (A : Over (Sp R)) [GrpObj A] (T : Over (Sp R)) : (1 : T ⟶ A).left = T.hom ≫ η[A].left := rfl

theorem inl_w (A : Over (Sp R)) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    (spMap (TrivSqZeroExt.inlHom B M) ≫ P) ≫ A.hom = (ovT R B M).hom := by
  rw [Category.assoc, hP]
  exact (GlobalTheory.Cris.spMap_comp _ _).symm

theorem fst_w (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ (ovT R B M).hom = (ovB R B).hom := by
  show _ ≫ spMap _ = spMap _
  rw [← GlobalTheory.Cris.spMap_comp]
  congr 1 <;> ext r <;> simp

theorem fst_inl (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap (TrivSqZeroExt.inlHom B M) = 𝟙 (Sp B) := by
  rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
  congr 1 <;> ext r <;> simp

def eFst (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : ovB R B ⟶ ovT R B M :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) (fst_w B M)

open Classical in

def tau (A : Over (Sp R)) [GrpObj A] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (z : Sp (TrivSqZeroExt B M) ⟶ A.left) :
    Sp (TrivSqZeroExt B M) ⟶ A.left :=
  if h : P ≫ A.hom = spMap (algebraMap R B) ∧ z ≫ A.hom = (ovT R B M).hom then
    ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P h.1) *
      Over.homMk (U := ovT R B M) (V := A) z h.2 : ovT R B M ⟶ A)).left
  else z

theorem tau_eq (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B))
    (z : Sp (TrivSqZeroExt B M) ⟶ A.left) (hz : z ≫ A.hom = (ovT R B M).hom) :
    tau A B M P z = ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) *
      Over.homMk (U := ovT R B M) (V := A) z hz : ovT R B M ⟶ A)).left := by
  rw [tau, dif_pos ⟨hP, hz⟩]

theorem red_iff (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (g : ovT R B M ⟶ A) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ g.left = P ↔
      eFst B M ≫ g = Over.homMk (U := ovB R B) (V := A) P hP := by
  constructor
  · intro h; ext; simpa [eFst] using h
  · intro h; have := congrArg CommaMorphism.left h; simpa [eFst] using this

theorem unit_eq (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B]
    (h : unitPt A B ≫ A.hom = spMap (algebraMap R B)) :
    Over.homMk (U := ovB R B) (V := A) (unitPt A B) h = 1 := by
  ext; rw [one_left]; rfl

end GlobalTheory.AbTan.Transl

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

theorem unit_w (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] :
    unitPt A B ≫ A.hom = spMap (algebraMap R B) := by
  rw [unitPt, Category.assoc, Over.w η[A]]
  exact Category.comp_id _

theorem bijOn_tau (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    Set.BijOn (tau A B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z} := by
  set Q : ovT R B M ⟶ A := Over.homMk (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) with hQ
  have hU := unit_w A B
  have keyQ : eFst B M ≫ Q = Over.homMk (U := ovB R B) (V := A) P hP := by
    ext
    simp only [eFst, Q, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, fst_inl]
    exact Category.id_comp _
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := hz
    show Lifts A.hom P (tau A B M P z)
    rw [tau_eq A P hP z h1]
    refine ⟨Over.w _, ?_⟩
    rw [red_iff A _ P hP, MonObj.comp_mul, keyQ,
      (red_iff A (Over.homMk (U := ovT R B M) (V := A) z h1) (unitPt A B) hU).1 h2, unit_eq, _root_.mul_one]
  · intro z1 hz1 z2 hz2 he
    obtain ⟨h11, -⟩ := hz1
    obtain ⟨h21, -⟩ := hz2
    rw [tau_eq A P hP z1 h11, tau_eq A P hP z2 h21] at he
    have := mul_left_cancel (Over.OverMorphism.ext he)
    exact congrArg CommaMorphism.left this
  · intro z' hz'
    obtain ⟨h1, h2⟩ := hz'
    set Z : ovT R B M ⟶ A := Q⁻¹ * Over.homMk (U := ovT R B M) (V := A) z' h1 with hZ
    refine ⟨Z.left, ⟨Over.w Z, ?_⟩, ?_⟩
    · rw [red_iff A Z (unitPt A B) hU, unit_eq, hZ, MonObj.comp_mul, GrpObj.comp_inv, keyQ,
        (red_iff A (Over.homMk (U := ovT R B M) (V := A) z' h1) P hP).1 h2, inv_mul_cancel]
    · show tau A B M P Z.left = z'
      rw [tau_eq A P hP Z.left (Over.w Z)]
      have e : Over.homMk (U := ovT R B M) (V := A) Z.left (Over.w Z) = Z := by ext; rfl
      rw [← hQ, e, hZ, mul_inv_cancel_left]
      rfl

theorem tau_natural (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] {B' M' : Type} [CommRing B'] [Algebra R B']
    [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (hβ : IsSum β α f) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) (z : Sp (TrivSqZeroExt B M) ⟶ A.left)
    (hz : Lifts A.hom (unitPt A B) z) :
    Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧
      tau A B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ tau A B M P z := by
  obtain ⟨hz1, hz2⟩ := hz
  have hβinl : β.comp (TrivSqZeroExt.inlHom B M) = (TrivSqZeroExt.inlHom B' M').comp (α : B →+* B') :=
    RingHom.ext fun b => hβ.1 b
  have hβT : β.comp ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) =
      (TrivSqZeroExt.inlHom B' M').comp (algebraMap R B') := by
    rw [← RingHom.comp_assoc, hβinl, RingHom.comp_assoc, AlgHom.comp_algebraMap]
  have hβfst : (TrivSqZeroExt.fstHom B' B' M').toRingHom.comp β =
      (α : B →+* B').comp (TrivSqZeroExt.fstHom B B M).toRingHom := by
    ext x
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    simp [map_add, hβ.1, hβ.2]
  let b : ovT R B' M' ⟶ ovT R B M := Over.homMk (spMap β) (by
    show spMap β ≫ spMap _ = spMap _
    rw [← GlobalTheory.Cris.spMap_comp, hβT])
  set Z : ovT R B M ⟶ A := Over.homMk z hz1 with hZ
  have hz' : (spMap β ≫ z) ≫ A.hom = (ovT R B' M').hom := Over.w (b ≫ Z)
  have hP' : (spMap (α : B →+* B') ≫ P) ≫ A.hom = spMap (algebraMap R B') := by
    rw [Category.assoc, hP, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  refine ⟨⟨hz', ?_⟩, ?_⟩
  · rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hβfst, GlobalTheory.Cris.spMap_comp, Category.assoc, hz2, unitPt,
      unitPt, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [tau_eq A _ hP' _ hz', tau_eq A P hP z hz1]
    have e1 : b ≫ (Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP)) =
        Over.homMk (U := ovT R B' M') (V := A) (spMap (TrivSqZeroExt.inlHom B' M') ≫ spMap (α : B →+* B') ≫ P)
          (inl_w A _ hP') := by
      ext
      simp only [b, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp, hβinl]
    have e2 : b ≫ Z = Over.homMk (U := ovT R B' M') (V := A) (spMap β ≫ z) hz' := by ext; rfl
    show _ = (b ≫ (_ * Z)).left
    rw [MonObj.comp_mul, e1, e2]

end GlobalTheory.AbTan.Transl

open GlobalTheory.AbTan.Transl in

theorem GlobalTheory.AbTan.exists_translation : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∃ τ : ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M], (Sp B ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left), (∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → Set.BijOn (τ B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z}) ∧ ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (B' M' : Type) [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f → ∀ (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → ∀ z, Lifts A.hom (unitPt A B) z → Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧ τ B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ τ B M P z := by
  intro R _ A _
  refine ⟨fun B M => tau A B M, ?_, ?_⟩
  · intro B M _ _ _ _ _ _ P hP
    exact bijOn_tau A P hP
  · intro B M _ _ _ _ _ _ B' M' _ _ _ _ _ _ α f β hβ P hP z hz
    exact tau_natural A α f β hβ P hP z hz
