import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq

noncomputable section

open NumberField NumberField.mixedEmbedding Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Cm

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def mixRing : Cinf E ≃+* mixedSpace E := (infEq E).trans (InfiniteAdeleRing.ringEquiv_mixedSpace E)

variable {E} in
omit [NumberField E] in
theorem infEq_apply (x : Cinf E) (w : InfinitePlace E) :
    infEq E x w = (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (x w) := rfl

variable {E} in
theorem mixRing_snd (x : Cinf E) (w : {w : InfinitePlace E // w.IsComplex}) : (mixRing E x).2 w = x w.1 :=
  (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2).apply_symm_apply (x w.1)

variable {E} in
theorem mixed_ext {x y : mixedSpace E} (h : ∀ w, x.2 w = y.2 w) : x = y :=
  Prod.ext (funext fun w => absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1)))
    (funext h)

def mixEq : Cinf E ≃ₐ[ℝ] mixedSpace E :=
  AlgEquiv.ofRingEquiv (f := mixRing E) fun _ => mixed_ext fun w => mixRing_snd _ w

def matEq : Matrix (Fin a) (Fin a) (Cinf E) ≃ₐ[ℝ] ArchMatrix E a := (mixEq E).mapMatrix

variable {E a} in
theorem matEq_apply (x : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) :
    (matEq E a x : Matrix (Fin a) (Fin a) (mixedSpace E)) i j = mixEq E (x i j) := rfl

def lieEq : Lie E a ≃ₗ[ℝ] (isExpLieAlgebra E a).lieSubalgebra where
  toFun X := ⟨matEq E a (Matrix.of X), Submodule.mem_top⟩
  invFun Y := toL ((matEq E a).symm Y.1)
  map_add' X Y := Subtype.ext (map_add (matEq E a) (Matrix.of X) (Matrix.of Y))
  map_smul' c X := Subtype.ext (map_smul (matEq E a) c (Matrix.of X))
  left_inv X := (matEq E a).symm_apply_apply (Matrix.of X)
  right_inv Y := Subtype.ext ((matEq E a).apply_symm_apply Y.1)

def grpEq : GL (Fin a) (Cinf E) ≃* archGroup E a :=
  (Units.mapEquiv (matEq E a).toMulEquiv).trans Subgroup.topEquiv.symm

variable {E a}

@[simp] theorem coe_lieEq (X : Lie E a) : (lieEq E a X : ArchMatrix E a) = matEq E a (Matrix.of X) := rfl

@[simp] theorem coe_grpEq (y : GL (Fin a) (Cinf E)) :
    (((grpEq E a y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) = matEq E a y.val := rfl

theorem lieEq_oneL : (lieEq E a (oneL E a) : ArchMatrix E a) = 1 := map_one (matEq E a)

theorem lieEq_lie (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    lieEq E a (toL (X * Y - Y * X)) = ⁅lieEq E a (toL X), lieEq E a (toL Y)⁆ := by
  refine Subtype.ext ?_
  change matEq E a (X * Y - Y * X) = _
  rw [map_sub, map_mul, map_mul]
  rfl

theorem infGL_entry (y : GL (Fin a) (Cinf E)) (i j : Fin a) : ((infGL E a y).val i j).1 = infEq E (y.val i j) :=
  ((infEq E).apply_symm_apply _).symm.trans
    (congrArg (fun g : GL (Fin a) (Cinf E) => infEq E (g.val i j)) (pInf_infGL y))

theorem infEmb_grpEq (y : GL (Fin a) (Cinf E)) : infEmb E a (grpEq E a y) = infGL E a y := by
  refine (AdelicGLn.prodEquiv E a).injective ?_
  rw [prodEquiv_infEmb]
  refine Prod.ext ?_ (pFin_infGL y).symm
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm_apply_apply (infEq E (y.val i j))).trans
    (infGL_entry y i j).symm

end UpperTheory.V.Cm
