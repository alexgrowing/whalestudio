import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeB

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.UnitB

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

def toG (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset ε) : Formalism.REAL.UJ ε :=
  ⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, (Formalism.REAL.indefinite_unitary_inv_closed n ε g hg).1,
    (Formalism.REAL.indefinite_unitary_inv_closed n ε g hg).2⟩, hg⟩

theorem umat_toG (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset ε) : Formalism.MainNotions.S.umat (toG g hg) = g := rfl

theorem umat_mul (a b : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl

theorem umat_one : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl

def ex (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) (s : ℝ) : Formalism.REAL.UJ ε :=
  toG (NormedSpace.exp ((s : ℂ) • X)) (exp_smul_mem_UJset hX s)

theorem umat_ex {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) :
    Formalism.MainNotions.S.umat (ex X hX s) = NormedSpace.exp ((s : ℂ) • X) := rfl

theorem ex_zero {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : ex X hX 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show Formalism.MainNotions.S.umat (ex X hX 0) = Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)
  rw [umat_ex, umat_one, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]

theorem ex_add {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s t : ℝ) :
    ex X hX (s + t) = ex X hX s * ex X hX t := by
  apply Subtype.ext
  apply Units.ext
  show Formalism.MainNotions.S.umat (ex X hX (s + t)) = Formalism.MainNotions.S.umat (ex X hX s * ex X hX t)
  rw [umat_mul, umat_ex, umat_ex, umat_ex, Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_expm (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) (NormedSpace.exp ((t : ℂ) • X) * X) t := by
  have h := hasDerivAt_exp_smul_const X t
  rw [show (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X)) = fun s : ℝ => NormedSpace.exp (s • X) from
    funext fun s => by rw [Complex.coe_smul], Complex.coe_smul]
  exact h

theorem continuous_ex {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : Continuous (ex X hX) := by
  have h1 : Continuous (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X)) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_expm X s).continuousAt
  unfold ex toG
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, ?_⟩) _
  show Continuous fun s : ℝ => Formalism.REAL.Jm ε * (NormedSpace.exp ((s : ℂ) • X))ᴴ * Formalism.REAL.Jm ε
  exact (continuous_const.mul h1.matrix_conjTranspose).mul continuous_const

theorem hasDerivAt_wt (dual : Bool) (ξ c : Fin n) (Y X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => wt dual ε ξ (Y * NormedSpace.exp ((t : ℂ) • X)) c) (wt dual ε ξ (Y * X) c) 0 := by
  have h1 := (hasDerivAt_expm X 0).const_mul Y
  rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul] at h1
  exact (LinearMap.toContinuousLinearMap (wtLin dual ε ξ c)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

end Deriv

theorem inG_entry {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (a b : Fin n) :
    sg ε a * star (X b a) = -(sg ε b * X a b) := by
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h := congrFun (congrFun hX' a) b
  simp only [Matrix.add_apply, Matrix.zero_apply, Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply] at h
  have ha := sg_mul_self ε a
  have hb := sg_mul_self ε b
  linear_combination (sg ε a * sg ε b) * h - (sg ε a * star (X b a)) * hb - (sg ε b * X a b) * ha

theorem wt_deriv_id (dual : Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (ξ : Fin n)
    (Y : Matrix (Fin n) (Fin n) ℂ) (I : Fin n → ℂ) :
    ∑ c, wt dual ε ξ (Y * X) c * I c =
      ∑ c, wt dual ε ξ Y c * cond dual (-∑ a, X a c * I a) (∑ b, X c b * I b) := by
  cases dual
  · simp only [wt, cond_false, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
  · have key : ∀ b c, sg ε c * star (X b c) = -(sg ε b * X c b) := fun b c => inG_entry hX c b
    simp only [wt, cond_true, Matrix.mul_apply, star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    linear_combination (star (Y ξ b) * I c) * key b c

def mx {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Fin n → Fin n → Module.End ℂ W)
    (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ W := ∑ a, ∑ b, X a b • T a b

theorem mx_apply_tensF {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (X : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → M) (c : Fin n) :
    mx (tensF dual E) X f c = actM E X (f c) + cond dual (-∑ a, X a c • f a) (∑ b, X c b • f b) := by
  cases dual
  · simp [mx, tensF, tensV, actM, coordV, Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_ite,
      Finset.sum_apply, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single c]
    · simp
    · intro a _ ha
      rw [if_neg (Ne.symm ha)]
      simp
    · intro h
      exact absurd (Finset.mem_univ c) h
  · simp [mx, tensF, tensVd, actM, coordV, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib, smul_ite,
      Finset.sum_apply, LinearMap.sum_apply, sub_eq_add_neg]
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ite_apply, LinearMap.proj_apply,
      LinearMap.zero_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 2
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
      simp
    · intro h
      exact absurd (Finset.mem_univ c) h

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem sig_mul (hσ : IsURepOn (UJset ε) σ) (a b : Formalism.REAL.UJ ε) :
    σ (Formalism.MainNotions.S.umat (a * b)) = (σ (Formalism.MainNotions.S.umat a)).comp (σ (Formalism.MainNotions.S.umat b)) := by
  rw [umat_mul]
  exact hσ.1.2 _ a.2 _ b.2

theorem sig_inv_apply (hσ : IsURepOn (UJset ε) σ) (g : Formalism.REAL.UJ ε) (v : H) :
    σ (Formalism.MainNotions.S.umat g) (σ (Formalism.MainNotions.S.umat g⁻¹) v) = v := by
  have h := (sig_mul hσ g g⁻¹).symm
  rw [mul_inv_cancel, umat_one, hσ.1.1] at h
  have h2 := congrArg (fun L : H →L[ℂ] H => L v) h
  simpa using h2

theorem sig_inner (hσ : IsURepOn (UJset ε) σ) (g : Formalism.REAL.UJ ε) (a b : H) :
    inner ℂ (σ (Formalism.MainNotions.S.umat g) a) (σ (Formalism.MainNotions.S.umat g) b) = inner ℂ a b := by
  let L : H →ₗᵢ[ℂ] H :=
    { toLinearMap := (σ (Formalism.MainNotions.S.umat g) : H →ₗ[ℂ] H), norm_map' := hσ.2.1 _ g.2 }
  exact L.inner_map_map a b

theorem inner_sig (hσ : IsURepOn (UJset ε) σ) (g : Formalism.REAL.UJ ε) (y u : H) :
    inner ℂ y (σ (Formalism.MainNotions.S.umat g) u) = inner ℂ (σ (Formalism.MainNotions.S.umat g⁻¹) y) u := by
  rw [← sig_inner hσ g (σ (Formalism.MainNotions.S.umat g⁻¹) y) u, sig_inv_apply hσ g y]

theorem wt_K (dual : Bool) (ξ : Fin n) (x k : Matrix (Fin n) (Fin n) ℂ) (hk : k * Jm ε = Jm ε * k)
    (d : Fin n) : ∑ c, wt dual ε ξ x c * cond dual (star (k c d)) (k c d) = wt dual ε ξ (x * k) d := by
  cases dual
  · simp [wt, Matrix.mul_apply]
  · have hkc : ∀ c, sg ε c * star (k c d) = sg ε d * star (k c d) := by
      intro c
      have h := congrFun (congrFun hk c) d
      simp only [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
      have h2 := congrArg star h
      simp only [star_mul', star_sg] at h2
      linear_combination (-1 : ℂ) * h2
    simp only [wt, cond_true, Matrix.mul_apply, star_sum, star_mul', Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    linear_combination (star (x ξ c)) * hkc c

theorem cf_kDiag (hσ : IsURepOn (UJset ε) σ) (dual : Bool) (y : H) (ξ : Fin n) (F : Fin n → H)
    (κ : Formalism.REAL.UJ ε) (hk : Formalism.MainNotions.S.umat κ * Jm ε = Jm ε * Formalism.MainNotions.S.umat κ) (g : Formalism.REAL.UJ ε) :
    cf dual ε σ y ξ (kDiag dual σ (Formalism.MainNotions.S.umat κ) F) g = cf dual ε σ y ξ F (g * κ) := by
  unfold cf kDiag
  rw [sig_mul hσ g κ, umat_mul]
  simp only [ContinuousLinearMap.comp_apply, map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← wt_K dual ξ _ _ hk d, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

end Rep

section DerivRep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem inner_exp_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (y : H) (z : Formalism.REAL.UJ ε) (v : D) :
    HasDerivAt (fun t : ℝ => inner ℂ y (σ (Formalism.MainNotions.S.umat z * NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((actM E X v : D) : H))) 0 := by
  have h1 := hD.deriv X hX v
  have hfun : (fun t : ℝ => inner ℂ y (σ (Formalism.MainNotions.S.umat z * NormedSpace.exp ((t : ℂ) • X)) (v : H))) =
      fun t : ℝ => inner ℂ y (σ (Formalism.MainNotions.S.umat z) (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) := by
    funext t
    simp only [hσ.1.2 _ z.2 _ (exp_smul_mem_UJset hX t), ContinuousLinearMap.comp_apply]
  rw [hfun]
  exact (((innerSL ℂ y).comp (σ (Formalism.MainNotions.S.umat z))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

theorem hasDerivAt_matrixCoeff_flow (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (dual : Bool) (y : H) (ξ : Fin n) (f : Fin n → D)
    (z : Formalism.REAL.UJ ε) :
    HasDerivAt (fun s => cf dual ε σ y ξ (fun c => ((f c : D) : H)) (z * ex X hX s))
      (cf dual ε σ y ξ (fun c => ((mx (tensF dual E) X f c : D) : H)) z) 0 := by
  have hterm : ∀ c, HasDerivAt (fun s : ℝ => wt dual ε ξ (Formalism.MainNotions.S.umat z * NormedSpace.exp ((s : ℂ) • X)) c *
      inner ℂ y (σ (Formalism.MainNotions.S.umat z * NormedSpace.exp ((s : ℂ) • X)) ((f c : D) : H)))
      (wt dual ε ξ (Formalism.MainNotions.S.umat z * X) c * inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((f c : D) : H)) +
        wt dual ε ξ (Formalism.MainNotions.S.umat z) c * inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((actM E X (f c) : D) : H))) 0 := by
    intro c
    refine ((hasDerivAt_wt dual ξ c _ X).mul (inner_exp_deriv hσ hD hX y z (f c))).congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
  have hs := HasDerivAt.sum (u := (univ : Finset (Fin n))) (fun c _ => hterm c)
  rw [Finset.sum_fn] at hs
  have hv : cf dual ε σ y ξ (fun c => ((mx (tensF dual E) X f c : D) : H)) z =
      ∑ c, (wt dual ε ξ (Formalism.MainNotions.S.umat z * X) c * inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((f c : D) : H)) +
        wt dual ε ξ (Formalism.MainNotions.S.umat z) c * inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((actM E X (f c) : D) : H))) := by
    unfold cf
    simp only [mx_apply_tensF, Submodule.coe_add, map_add, inner_add_right, mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [wt_deriv_id dual hX ξ (Formalism.MainNotions.S.umat z) (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((f c : D) : H)))]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    cases dual
    · simp [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, inner_sum, inner_smul_right]
    · simp [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_neg, map_sum, map_smul, map_neg, inner_sum,
        inner_smul_right, inner_neg_right]
  rw [hv]
  exact hs

theorem hasDerivAt_cf (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (dual : Bool) (y : H) (ξ : Fin n) (f : Fin n → D)
    (x : Formalism.REAL.UJ ε) (t : ℝ) :
    HasDerivAt (fun s => cf dual ε σ y ξ (fun c => ((f c : D) : H)) (x * ex X hX s))
      (cf dual ε σ y ξ (fun c => ((mx (tensF dual E) X f c : D) : H)) (x * ex X hX t)) t := by
  have h0 := hasDerivAt_matrixCoeff_flow hσ hD hX dual y ξ f (x * ex X hX t)
  have h0' : HasDerivAt (fun u => cf dual ε σ y ξ (fun c => ((f c : D) : H)) (x * ex X hX t * ex X hX u))
      (cf dual ε σ y ξ (fun c => ((mx (tensF dual E) X f c : D) : H)) (x * ex X hX t)) (t - t) := by
    rw [sub_self]
    exact h0
  have h1 := h0'.comp_sub_const t t
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  beta_reduce
  rw [mul_assoc, ← ex_add, add_sub_cancel]

end DerivRep

end ReciprocityTheory.ChartRestriction.DS.UnitB
