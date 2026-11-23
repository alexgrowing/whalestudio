import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.IntegralHWMul

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep
open scoped ContDiff

namespace UpperTheory.V.Z.Inf.FourDH

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private def pairL (y : Lie K n) : Lie K n →L[ℝ] ℝ :=
  ∑ w : InfinitePlace K, ∑ a : Fin n, ∑ b : Fin n, Complex.reCLM.comp (y b a w •
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace K => ℂ) w).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Cinf K) b).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → Cinf K) a))))

private theorem pairL_eq (y x : Lie K n) : pairL y x = ∑ w, ∑ a, ∑ b, (y b a w * x a b w).re := by
  simp only [pairL, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, Complex.reCLM_apply, smul_eq_mul]

private theorem pairL_apply (y x : Lie K n) : pairL y x = ∑ w, ((Matrix.of x * Matrix.of y).trace w).re := by
  rw [pairL_eq]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.of_apply,
    Complex.re_sum, mul_comm]

private theorem sum_atEmb (τ : K →+* ℂ) (c : Cinf K) (z : ℂ) :
    ∑ w, (c w * atEmb τ z w).re = (coord τ c * z).re := by
  classical
  rw [Finset.sum_eq_single (InfinitePlace.mk τ)]
  · unfold coord atEmb
    split_ifs <;> simp
  · intro w _ hw
    unfold atEmb
    split_ifs <;> simp [Pi.single_eq_of_ne hw]
  · simp

private theorem pairL_single (y : Lie K n) (τ : K →+* ℂ) (i j : Fin n) (z : ℂ) :
    pairL y (toL (Matrix.single i j (atEmb τ z))) = (coord τ (y j i) * z).re := by
  rw [pairL_eq, ← sum_atEmb]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Matrix.single_apply, hb.symm]
  · simp
  · intro a _ ha
    simp [Matrix.single_apply, ha.symm]
  · simp

private def expF (e : ℝ) (y : Lie K n) (x : Lie K n) : ℂ := Complex.exp (Complex.I * e * (pairL y x : ℂ))

private theorem four_eq (e : ℝ) (Φ : Lie K n → ℂ) (y : Lie K n) : four e Φ y = ∫ x, Φ x * expF e y x := by
  simp only [four, expF, pairL_apply, Complex.ofReal_mul, mul_assoc]

private theorem hasFDerivAt_expF (e : ℝ) (y : Lie K n) (a : ℂ) (x : Lie K n) :
    HasFDerivAt (fun x => a * expF e y x)
      (a • (expF e y x • ((Complex.I * e) • (Complex.ofRealCLM.comp (pairL y))))) x := by
  have h1 : HasFDerivAt (fun x : Lie K n => Complex.I * e * (pairL y x : ℂ))
      ((Complex.I * e) • (Complex.ofRealCLM.comp (pairL y))) x :=
    ((Complex.ofRealCLM.comp (pairL y)).hasFDerivAt).const_mul _
  exact (h1.cexp).const_mul a

private theorem contDiff_expF (e : ℝ) (y : Lie K n) : ContDiff ℝ ∞ (expF e y) := by
  unfold expF
  exact Complex.contDiff_exp.comp (contDiff_const.mul ((Complex.ofRealCLM.comp (pairL y)).contDiff))

private theorem pd_expF (e : ℝ) (y : Lie K n) (a : ℂ) (τ : K →+* ℂ) (i j : Fin n) :
    pd τ i j (fun x => a * expF e y x) = fun x => (a * (Complex.I * e / 2 * coord τ (y j i))) * expF e y x := by
  funext x
  rw [pd, (hasFDerivAt_expF e y a x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, pairL_single, smul_eq_mul, mul_one, Complex.mul_I_re, Complex.ofReal_neg]
  conv_rhs => rw [← Complex.re_add_im (coord τ (y j i))]
  ring

private theorem foldr_expF (e : ℝ) (y : Lie K n) (τ : K →+* ℂ) (p : Equiv.Perm (Fin n)) (l : List (Fin n)) (a : ℂ) :
    l.foldr (fun j G => pd τ (p j) j G) (fun x => a * expF e y x) =
      fun x => (a * (l.map fun j => Complex.I * e / 2 * coord τ (y j (p j))).prod) * expF e y x := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    rw [List.foldr_cons, ih, pd_expF]
    funext x
    simp only [List.map_cons, List.prod_cons]
    ring

omit [NumberField K] in
private theorem detAt_eq (τ : K →+* ℂ) (y : Lie K n) :
    detAt τ y = ∑ p : Equiv.Perm (Fin n), (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * ∏ j, coord τ (y j (p j)) := by
  rw [detAt, (coord τ).map_det, ← Matrix.det_transpose, Matrix.det_apply']
  rfl

private theorem detD_expF (e : ℝ) (y : Lie K n) (τ : K →+* ℂ) :
    detD τ (expF e y) = fun x => ((Complex.I * e / 2) ^ n * detAt τ y) * expF e y x := by
  funext x
  have h : expF e y = fun x => 1 * expF e y x := by simp
  rw [detD, h]
  simp only [foldr_expF, detAt_eq, ← Fin.prod_univ_def, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

variable [IsTotallyComplex K]

private theorem four_detD (e : ℝ) (τ : K →+* ℂ) (Φ : Lie K n → ℂ) (hΦ : IsTest Φ) (y : Lie K n) :
    four e (detD τ Φ) y = (-(Complex.I * e / 2)) ^ n * detAt τ y * four e Φ y := by
  have hp := (parts K n τ Φ hΦ).2 (expF e y) (contDiff_expF e y).contDiffOn
  rw [four_eq, four_eq, hp, detD_expF]
  simp_rw [mul_left_comm (Φ _) (_ ^ n * _)]
  rw [integral_const_mul, neg_pow (Complex.I * e / 2)]
  ring

private theorem four_foldr (e : ℝ) (L : List (K →+* ℂ)) (Φ : Lie K n → ℂ) (hΦ : IsTest Φ) :
    IsTest (L.foldr detD Φ) ∧ ∀ y, four e (L.foldr detD Φ) y =
      (-(Complex.I * e / 2)) ^ (n * L.length) * (L.map fun τ => detAt τ y).prod * four e Φ y := by
  induction L with
  | nil => simp [hΦ]
  | cons τ L ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨(parts K n τ _ h1).1, fun y => ?_⟩
    rw [List.foldr_cons, four_detD e τ _ h1, h2 y]
    simp only [List.length_cons, List.map_cons, List.prod_cons]
    ring

private theorem prod_coord (c : Cinf K) : ∏ τ : K →+* ℂ, coord τ c = ((∏ w, ‖c w‖ ^ 2 : ℝ) : ℂ) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  have hf : (Finset.univ.filter fun τ : K →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · right; rw [h]; simp
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.prod_pair hne.symm]
  unfold coord
  rw [if_pos (by rw [InfinitePlace.mk_embedding]),
    if_neg (by rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]; exact hne.symm)]
  simp [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq, Complex.mul_conj']

end UpperTheory.V.Z.Inf.FourDH

open UpperTheory.V.Z.Inf.FourDH in
theorem UpperTheory.V.Z.Inf.fourD :
    UpperTheory.V.Z.Inf.FourD := by
  intro K _ _ _ n e he
  refine ⟨(-(Complex.I * e / 2)) ^ (n * (Finset.univ : Finset (K →+* ℂ)).card), ?_, fun Φ hΦ y => ?_⟩
  · refine pow_ne_zero _ ?_
    simp [he, Complex.I_ne_zero]
  · rw [detAll, (four_foldr e _ Φ hΦ).2 y, Finset.length_toList, Finset.prod_map_toList]
    simp only [detAt, prod_coord, nrm]
