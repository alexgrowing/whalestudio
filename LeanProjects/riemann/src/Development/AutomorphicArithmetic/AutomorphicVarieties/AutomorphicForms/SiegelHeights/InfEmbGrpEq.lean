import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces

noncomputable section

open NumberField NumberField.mixedEmbedding Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Fb

variable (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ)

def mixRing : TR.Rinf E ≃+* mixedSpace E := (TR.infEq E).trans (InfiniteAdeleRing.ringEquiv_mixedSpace E)

variable {E} in
theorem mixRing_fst (x : TR.Rinf E) (w : {w : InfinitePlace E // w.IsReal}) : (mixRing E x).1 w = x w.1 :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal w.2).apply_symm_apply (x w.1)

variable {E} in
theorem mixed_ext {x y : mixedSpace E} (h : ∀ w, x.1 w = y.1 w) : x = y :=
  Prod.ext (funext h) (funext fun w => absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2))

def mixEq : TR.Rinf E ≃ₐ[ℝ] mixedSpace E :=
  AlgEquiv.ofRingEquiv (f := mixRing E) fun _ => mixed_ext fun w => mixRing_fst _ w

def matEq : Matrix (Fin a) (Fin a) (TR.Rinf E) ≃ₐ[ℝ] ArchMatrix E a := (mixEq E).mapMatrix

variable {E a} in
theorem matEq_apply (x : Matrix (Fin a) (Fin a) (TR.Rinf E)) (i j : Fin a) :
    (matEq E a x : Matrix (Fin a) (Fin a) (mixedSpace E)) i j = mixEq E (x i j) := rfl

def lieEq : TR.Lie E a ≃ₗ[ℝ] (isExpLieAlgebra E a).lieSubalgebra where
  toFun X := ⟨matEq E a (Matrix.of X), Submodule.mem_top⟩
  invFun Y := TR.toL ((matEq E a).symm Y.1)
  map_add' X Y := Subtype.ext (map_add (matEq E a) (Matrix.of X) (Matrix.of Y))
  map_smul' c X := Subtype.ext (map_smul (matEq E a) c (Matrix.of X))
  left_inv X := (matEq E a).symm_apply_apply (Matrix.of X)
  right_inv Y := Subtype.ext ((matEq E a).apply_symm_apply Y.1)

def grpEq : GL (Fin a) (TR.Rinf E) ≃* archGroup E a :=
  (Units.mapEquiv (matEq E a).toMulEquiv).trans Subgroup.topEquiv.symm

variable {E a}

@[simp] theorem coe_lieEq (X : TR.Lie E a) : (lieEq E a X : ArchMatrix E a) = matEq E a (Matrix.of X) := rfl

@[simp] theorem coe_grpEq (y : GL (Fin a) (TR.Rinf E)) :
    (((grpEq E a y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) = matEq E a y.val := rfl

theorem lieEq_oneL : (lieEq E a (TR.oneL E a) : ArchMatrix E a) = 1 := map_one (matEq E a)

theorem lieEq_lie (X Y : TR.Lie E a) :
    lieEq E a (TR.toL (Matrix.of X * Matrix.of Y) - TR.toL (Matrix.of Y * Matrix.of X)) = ⁅lieEq E a X, lieEq E a Y⁆ := by
  refine Subtype.ext ?_
  change matEq E a (Matrix.of X * Matrix.of Y - Matrix.of Y * Matrix.of X) = _
  rw [map_sub, map_mul, map_mul]
  rfl

omit [IsTotallyReal E] in
theorem finEmb_eq : finEmb E a = finGL E a := by
  refine MonoidHom.ext fun k => (AdelicGLn.prodEquiv E a).injective ?_
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ ?_
  · exact (map_cornerGL_of_zero (sFin E) (RingHom.fst (InfiniteAdeleRing E) (Af E)) (fun _ => rfl) k).symm
  · exact (map_cornerGL_of_hom (sFin E) (pFin E) (RingHom.id _) (fun _ => rfl) k).symm

theorem infEmb_grpEq (y : GL (Fin a) (TR.Rinf E)) : infEmb E a (grpEq E a y) = TR.infGL E a y := by
  refine (AdelicGLn.prodEquiv E a).injective ?_
  rw [prodEquiv_infEmb]
  refine Prod.ext ?_ (TR.pFin_infGL y).symm
  refine Eq.trans ?_ (map_cornerGL_of_hom (TR.sInf E) (RingHom.fst (InfiniteAdeleRing E) (Af E))
    (TR.infEq E).toRingHom (fun _ => rfl) y).symm
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm_apply_apply (TR.infEq E (y.val i j))

end UpperTheory.V.Fb
