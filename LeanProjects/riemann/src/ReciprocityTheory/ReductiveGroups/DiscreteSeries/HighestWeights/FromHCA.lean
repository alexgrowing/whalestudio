import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelDer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PolyCoef

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Sig

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

open Classical in

def fhSig (τ : KG ε →* unitary (V →L[ℂ] V)) (g : Matrix (Fin n) (Fin n) ℂ) : V →L[ℂ] V :=
  if h : g ∈ Kset ε then ((τ (torepK ε h) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) else 1

lemma fhSig_of_mem (τ : KG ε →* unitary (V →L[ℂ] V)) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    fhSig τ g = ((τ (torepK ε hg) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
  unfold fhSig
  rw [dif_pos hg]

lemma fhSig_toMK (τ : KG ε →* unitary (V →L[ℂ] V)) (k : KG ε) :
    fhSig τ (toMK k) = ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
  rw [fhSig_of_mem τ (g := toMK k) k.2, torepK_toMK]

lemma fh_op_mul (τ : KG ε →* unitary (V →L[ℂ] V)) (k k' : KG ε) :
    ((τ (k * k') : unitary (V →L[ℂ] V)) : V →L[ℂ] V) =
      ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V).comp ((τ k' : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
  rw [map_mul]
  rfl

lemma fhSig_isURepOn (τ : KG ε →* unitary (V →L[ℂ] V)) (hτ : Continuous τ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) (fhSig τ) := by
  have hmul : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, a * b ∈ Kset ε := by
    intro a ha b hb
    refine ⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩
    rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
    ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [fhSig_of_mem τ hone]
    have h1 : torepK ε hone = 1 := onep_KG_ext (by rw [toMK_torepK]; rfl)
    rw [h1, map_one]
    rfl
  · intro a ha b hb
    rw [fhSig_of_mem τ ha, fhSig_of_mem τ hb, fhSig_of_mem τ (hmul a ha b hb)]
    have h1 : torepK ε (hmul a ha b hb) = torepK ε ha * torepK ε hb := onep_KG_ext (by
      rw [toMK_torepK]
      exact (congrArg₂ (· * ·) (toMK_torepK ε ha) (toMK_torepK ε hb)).symm)
    rw [h1, fh_op_mul]
  · intro g hg v
    rw [fhSig_of_mem τ hg]
    exact Unitary.norm_map _ v
  · intro v
    rw [continuousOn_iff_continuous_restrict]
    show Continuous fun x : ↥(Kset ε) => fhSig τ (x : Matrix (Fin n) (Fin n) ℂ) v
    have hc : Continuous fun x : ↥(Kset ε) =>
        ((τ (torepK ε x.2) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v :=
      (continuous_subtype_val.comp (hτ.comp (continuous_torepK ε))).clm_apply continuous_const
    refine hc.congr fun x => ?_
    rw [fhSig_of_mem τ x.2]

end Sig

section InK

variable {n : ℕ} {ε : Fin n → Bool}

end InK

section Coef

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k : ℕ}

def fhEnt (k : ℕ) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] (Fin k × Fin k → ℂ) where
  toFun A ij := A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma fh_diff_eval (P : MvPolynomial (Fin k × Fin k) ℂ) (A : Matrix (Fin k) (Fin k) ℂ) :
    DifferentiableAt ℂ (fun A : Matrix (Fin k) (Fin k) ℂ => MvPolynomial.eval (fhEnt k A) P) A := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C]
    exact differentiableAt_const _
  next p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  next p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (differentiableAt_pi.1
      (LinearMap.toContinuousLinearMap (fhEnt k)).differentiableAt i)

lemma fh_det_eq (A : Matrix (Fin k) (Fin k) ℂ) :
    A.det = MvPolynomial.eval (fhEnt k A) (Matrix.det (Matrix.mvPolynomialX (Fin k) (Fin k) ℂ)) := by
  have h : (fhEnt k A : Fin k × Fin k → ℂ) = fun p => A p.1 p.2 := rfl
  rw [h, RingHom.map_det, Matrix.mvPolynomialX_mapMatrix_eval]

end Coef

section Coef2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V]

lemma fh_det_ne_zero {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Kset (fun _ : Fin k => true)) : g.det ≠ 0 := by
  intro h0
  have hu := Matrix.mem_unitaryGroup_iff.1 hg.1
  have h := congrArg Matrix.det hu
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
  exact zero_ne_one h

theorem fh_coef (τ : KG (fun _ : Fin k => true) →* unitary (V →L[ℂ] V)) (hτ : Continuous τ) (v w : V) :
    ∃ L : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] ℂ, ∀ X, inK (fun _ : Fin k => true) X →
      inner ℂ w (derOp (fun _ : Fin k => true) τ X v) = L X := by
  classical
  obtain ⟨m, P, hP⟩ := polynomial_coefficients k V (fhSig τ) ⊤ (fhSig_isURepOn τ hτ) inferInstance
    (fun _ _ _ _ => Submodule.mem_top) v Submodule.mem_top w
  have hdet1 : DifferentiableAt ℂ (fun A : Matrix (Fin k) (Fin k) ℂ => A.det) 1 := by
    have h : (fun A : Matrix (Fin k) (Fin k) ℂ => A.det) = fun A =>
        MvPolynomial.eval (fhEnt k A) (Matrix.det (Matrix.mvPolynomialX (Fin k) (Fin k) ℂ)) :=
      funext fh_det_eq
    rw [h]
    exact fh_diff_eval _ _
  let F : Matrix (Fin k) (Fin k) ℂ → ℂ := fun A =>
    MvPolynomial.eval (fhEnt k A) P * (A.det ^ m)⁻¹
  have hF : DifferentiableAt ℂ F 1 := by
    have hne : (1 : Matrix (Fin k) (Fin k) ℂ).det ^ m ≠ 0 := by
      rw [Matrix.det_one, one_pow]
      exact one_ne_zero
    have hpow : DifferentiableAt ℂ (fun A : Matrix (Fin k) (Fin k) ℂ => A.det ^ m) 1 :=
      (differentiableAt_pow m).comp 1 hdet1
    exact (fh_diff_eval P 1).mul (hpow.inv hne)
  refine ⟨(fderiv ℂ F 1).toLinearMap, fun X hX => ?_⟩
  have hγ := (kcurve_spec (fun _ : Fin k => true) hX).2.1
  have hD := derOp_hasDeriv (fun _ : Fin k => true) τ hτ X hX (kcurve (fun _ : Fin k => true) X) hγ
  let Λ : (V →L[ℂ] V) →L[ℂ] ℂ := (innerSL ℂ w).comp (ContinuousLinearMap.apply ℂ V v)
  have h1 := (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hD
  have he := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at he
  have h3 := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 he (by simp)
  have heq : (⇑(Λ.restrictScalars ℝ) ∘ fun t : ℝ =>
      ((τ (kcurve (fun _ : Fin k => true) X t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) =
      F ∘ fun u : ℝ => NormedSpace.exp (u • X) := by
    funext t
    have hx : NormedSpace.exp (t • X) = toMK (kcurve (fun _ : Fin k => true) X t) := by
      rw [hγ t]
      exact congrArg NormedSpace.exp (Complex.coe_smul t X).symm
    simp only [Function.comp_apply]
    rw [hx]
    have hk : toMK (kcurve (fun _ : Fin k => true) X t) ∈ Kset (fun _ : Fin k => true) := (kcurve (fun _ : Fin k => true) X t).2
    have hP' := hP _ hk
    rw [fhSig_toMK] at hP'
    simp only [Λ, F, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, innerSL_apply_apply]
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ (fh_det_ne_zero hk))]
    exact hP'
  rw [heq] at h1
  have h4 := h1.unique h3
  exact h4

end Coef2

end ReciprocityTheory.ChartRestriction.DS.HW
