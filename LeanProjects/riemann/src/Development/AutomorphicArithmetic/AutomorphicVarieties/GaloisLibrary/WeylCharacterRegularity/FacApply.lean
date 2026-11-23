import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.IsRegConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh Topology

namespace UpperTheory.V.WeylC

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def fac (P : Weyl.Pre a) (N : ℕ) (τ : E →+* ℂ) : GL (Fin a) (Cinf E) →* Matrix (Fin P.d) (Fin P.d) ℂ where
  toFun y := (coord τ y.val.det)⁻¹ ^ N • P.mat (y.val.map (coord τ))
  map_one' := by simp
  map_mul' y z := by
    simp only [Units.val_mul, Matrix.det_mul, map_mul, Matrix.map_mul, mul_inv, mul_pow, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_comm]

omit [NumberField E] in
theorem fac_apply (P : Weyl.Pre a) (N : ℕ) (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) (i j : Fin P.d) :
    fac P N τ y i j = (coord τ y.val.det)⁻¹ ^ N * P.mat (y.val.map (coord τ)) i j := rfl

omit [NumberField E] in
theorem isReg_fac (P : Weyl.Pre a) (N : ℕ) (τ : E →+* ℂ) : IsReg (fac P N τ) := fun i j => by
  obtain ⟨p, hp⟩ := P.poly i j
  have h1 : ∀ q : MvPolynomial (Fin a × Fin a) ℂ, (fun y : GL (Fin a) (Cinf E) =>
      MvPolynomial.eval (fun ab => coord τ (y.val ab.1 ab.2)) q) ∈ regFun E a := fun q => by
    induction q using MvPolynomial.induction_on with
    | C c => simp only [MvPolynomial.eval_C]; exact (regFun E a).algebraMap_mem c
    | add p q hp hq => simp only [map_add]; exact (regFun E a).add_mem hp hq
    | mul_X p n hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact (regFun E a).mul_mem hp (Algebra.subset_adjoin (Or.inl ⟨τ, n.1, n.2, rfl⟩))
  have h2 : (fun y : GL (Fin a) (Cinf E) => (coord τ y.val.det)⁻¹) ∈ regFun E a :=
    Algebra.subset_adjoin (Or.inr ⟨τ, rfl⟩)
  have h3 := (regFun E a).mul_mem ((regFun E a).pow_mem h2 N) (h1 p)
  convert h3 using 1
  funext y
  simp [fac_apply, hp]

theorem diff_coef (P : Weyl.Pre a) (i j : Fin P.d) : Differentiable ℂ (P.coef i j) := by
  obtain ⟨p, hp⟩ := P.poly i j
  have e : P.coef i j = fun x => MvPolynomial.eval (fun ab : Fin a × Fin a => x ab.1 ab.2) p := funext fun x => hp _
  rw [e]
  clear e hp
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (by fun_prop : Differentiable ℂ fun x : Fin a → Fin a → ℂ => x n.1 n.2)

theorem dOf_fac (P : Weyl.Pre a) (N : ℕ) (τ : E →+* ℂ) (X : Lie E a) :
    dOf (fac P N τ) X = P.D ((Matrix.of X).map (coord τ)) - ((N : ℂ) * coord τ (Matrix.of X).trace) • 1 := by
  ext i j
  let L : Lie E a →L[ℝ] (Fin a → Fin a → ℂ) :=
    ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun l => (coordL τ).comp ((ContinuousLinearMap.proj l).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) k))
  have hL : L (oneL E a) = Weyl.oneM a := by
    funext k l
    exact congrFun (congrFun (Matrix.map_one (coord τ) (map_zero _) (map_one _)) k) l
  have h1 : HasFDerivAt (fun x => P.coef i j (L x))
      (((fderiv ℂ (P.coef i j) (Weyl.oneM a)).restrictScalars ℝ).comp L) (oneL E a) :=
    HasFDerivAt.comp (g := P.coef i j) (oneL E a)
      (by rw [hL]; exact (diff_coef P i j _).hasFDerivAt.restrictScalars ℝ) L.hasFDerivAt
  have h2 := (coordL τ).hasFDerivAt.comp (oneL E a) (contDiff_det.differentiable (by simp) (oneL E a)).hasFDerivAt
  have hd : (Matrix.of (oneL E a)).det = 1 := Matrix.det_one
  have h3 := ((hasDerivAt_inv (x := coordL τ (Matrix.of (oneL E a)).det) (by simp [hd])).pow N).hasFDerivAt.restrictScalars ℝ
  have h4 := (h3.comp (oneL E a) h2).mul h1
  have h5 := h4.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => fac P N τ y i j)
    (fun y => rfl) (x := oneL E a) isUnit_one)
  rw [dOf, Matrix.of_apply, h5.fderiv]
  have h6 : P.coef i j (Weyl.oneM a) = (1 : Matrix _ _ ℂ) i j := congrFun (congrFun (map_one P.mat) i) j
  have h7 : P.D ((Matrix.of X).map (coord τ)) i j = fderiv ℂ (P.coef i j) (Weyl.oneM a) (L X) := rfl
  simp [hd, hL, h6, h7, fderiv_det_one]
  ring

open Classical in
theorem eOf_fac [IsTotallyComplex E] (P : Weyl.Pre a) (N : ℕ) (τ' τ : E →+* ℂ) (i j : Fin a) :
    eOf (fac P N τ') τ i j =
      if τ' = τ then P.E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0) else 0 := by
  have h1 : ∀ x : Cinf E, dOf (fac P N τ') (toL (Matrix.single i j x)) =
      coord τ' x • (P.E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0)) := fun x => by
    have e0 : Matrix.of (toL (Matrix.single i j x)) = Matrix.single i j x := rfl
    have e : (Matrix.single i j x).map (coord τ') = coord τ' x • Matrix.single i j 1 := by
      ext k l
      simp [Matrix.single_apply, apply_ite (coord τ')]
    rw [dOf_fac, e0, e, map_smul, Weyl.Pre.E, smul_add, sub_eq_add_neg]
    congr 1
    split_ifs with h
    · subst h; simp [Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
    · simp [h]
  rw [eOf, h1, h1, smul_smul, ← sub_smul, smul_smul, coord_hol]
  split_ifs <;> simp

end UpperTheory.V.WeylC
