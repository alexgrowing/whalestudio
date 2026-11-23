import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.RatSlash

variable {F : Type} [Field F] [NumberField F]

theorem cmp_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v).toMonoidHom t) * cmp v h := by
  rw [map_mul]
  congr 1
  ext i j
  simp [cmp, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem det_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det =
      (t : InfinitePlace F → ℝ) ^ 2 * (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_mul]

theorem unit_ne (t : (InfinitePlace F → ℝ)ˣ) (v : InfinitePlace F) : (t : InfinitePlace F → ℝ) v ≠ 0 := fun h0 => by
  have := congrFun t.mul_inv v
  simp [h0] at this

theorem denom_scalar_mul (u : ℝˣ) (g : GL (Fin 2) ℝ) (z : ℂ) :
    UpperHalfPlane.denom (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) z = ((u : ℝ) : ℂ) * UpperHalfPlane.denom g z := by
  simp [UpperHalfPlane.denom, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem sl_scalar_mul {k : ℕ} (hk : Even k) (f : Hn F → ℂ) (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f := by
  obtain ⟨m, rfl⟩ := hk
  funext z
  have hact : act (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) z = act h z := by
    unfold act
    funext v
    rw [cmp_scalar_mul, mul_smul, UpperHalfPlane.glScalar_smul]
  have hdet : ∏ v, |((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| =
      (∏ v, (t : InfinitePlace F → ℝ) v) ^ 2 * ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| := by
    rw [det_scalar_mul, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    simp [abs_mul, sq_abs]
  have hden : ∏ v, UpperHalfPlane.denom (cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h)) (z v) =
      ((∏ v, (t : InfinitePlace F → ℝ) v : ℝ) : ℂ) * ∏ v, UpperHalfPlane.denom (cmp v h) (z v) := by
    simp_rw [cmp_scalar_mul, denom_scalar_mul]
    rw [Finset.prod_mul_distrib]
    push_cast
    simp
  have hP : (∏ v, (t : InfinitePlace F → ℝ) v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => unit_ne t v)
  have hQ : 0 ≤ ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| :=
    Finset.prod_nonneg (fun v _ => abs_nonneg _)
  have hexp : (((m + m : ℕ) : ℝ) / 2) = ((m : ℕ) : ℝ) := by
    push_cast
    ring
  unfold sl sl0
  rw [hact, hdet, hden, Real.mul_rpow (by positivity) hQ, hexp, Real.rpow_natCast, ← pow_mul]
  set P := ∏ v, (t : InfinitePlace F → ℝ) v
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  push_cast
  rw [mul_inv, mul_pow, inv_pow (P : ℂ)]
  field_simp
  ring

variable [IsTotallyReal F]

theorem ofReal_rhom (v : InfinitePlace F) (x : F) : ((rhom x v : ℝ) : ℂ) = v.embedding x :=
  InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x

theorem rhom_apply (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := by
  unfold rhom reAt
  show InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x = (v.embedding x).re
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem ofReal_reAt (v : InfinitePlace F) (x : F) : ((reAt v x : ℝ) : ℂ) = v.embedding x := by
  rw [← rhom_apply, ofReal_rhom]

variable (F) in

def embEquiv : InfinitePlace F ≃ (F →+* ℂ) where
  toFun v := v.embedding
  invFun φ := InfinitePlace.mk φ
  left_inv v := InfinitePlace.mk_embedding v
  right_inv φ := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))

theorem prod_reAt (x : F) : ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∏ v : InfinitePlace F, v.embedding x = ∏ φ : F →+* ℂ, φ x :=
    Equiv.prod_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∏ φ : F →+* ℂ, φ x = ∏ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.prod_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast]

theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∑ v : InfinitePlace F, v.embedding x = ∑ φ : F →+* ℂ, φ x :=
    Equiv.sum_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.sum_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← trace_eq_sum_embeddings ℂ, eq_ratCast]

theorem det_toInf (γ : GL (Fin 2) F) :
    ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det = rhom γ.val.det := by
  rw [RingHom.map_det]; rfl

theorem toInf_scalar (η : Fˣ) : toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η) := by
  ext i j v
  simp [toInf, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem rat_slash : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  intro F _ _ _ k f
  refine ⟨rhom_apply, fun γ => ⟨?_, ?_⟩, fun hk t h hh => ⟨?_, sl_scalar_mul hk f t h⟩, toInf_scalar,
    fun x => ⟨prod_reAt x, sum_reAt x⟩⟩
  · unfold Pos TP
    rw [det_toInf]
    simp only [rhom_apply]
  · funext z
    unfold sl
    rw [det_toInf]
    simp only [rhom_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.abs_prod, prod_reAt]
  · unfold Pos at hh ⊢
    intro v
    rw [det_scalar_mul]
    have h1 := unit_ne t v
    have h2 := hh v
    simp only [Pi.mul_apply, Pi.pow_apply]
    positivity

end GlobalTheory.HilbertThetaSeries.RatSlash

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_slash_rational_matrix_properties : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | exact GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | (intros; apply GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash <;> assumption)
