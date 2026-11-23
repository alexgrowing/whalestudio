import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.IntegralMulRightHaar

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.CxeAvg

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Ak (lam : Fin n → ℤ) (k : UK n) : EV n lam →L[ℂ] EV n lam := clm lam (fr0 lam k.1)

def Fk (lam : Fin n → ℤ) (k : UK n) : EV n lam →L[ℂ] EV n lam :=
  ContinuousLinearMap.adjoint (Ak lam k) * Ak lam k

theorem gramQ_def (lam : Fin n → ℤ) : gramQ lam = ∫ k, Fk lam k ∂(Measure.haar : Measure (UK n)) := rfl

theorem mem_GLs (k : UK n) : k.1 ∈ GLs n := (isUnit_det_unitary k).ne_zero

theorem Ak_mul (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) (k k' : UK n) : Ak lam (k * k') = Ak lam k * Ak lam k' := by
  unfold Ak
  rw [Submonoid.coe_mul, (hF n lam).2.1 _ _ (isUnit_det_unitary k) (isUnit_det_unitary k')]
  exact map_mul toEuclideanCLM _ _

theorem Ak_one (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) : Ak lam (1 : UK n) = 1 := by
  unfold Ak
  rw [OneMemClass.coe_one, (hF n lam).1]
  exact map_one toEuclideanCLM

theorem clm_continuous (lam : Fin n → ℤ) : Continuous (clm (n := n) lam) := by
  have h := LinearMap.continuous_of_finiteDimensional
    (toEuclideanCLM (n := Ix n lam) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
  exact h

theorem Ak_cont (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) : Continuous (Ak (n := n) lam) := by
  have hc : ContinuousOn (fr0 (n := n) lam) (GLs n) := (hF n lam).2.2.continuousOn
  exact (clm_continuous lam).comp
    (hc.comp_continuous continuous_subtype_val (fun k => mem_GLs k))

theorem Fk_cont (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) : Continuous (Fk (n := n) lam) := by
  have h := Ak_cont hF lam
  exact ((ContinuousLinearMap.adjoint : (EV n lam →L[ℂ] EV n lam) ≃ₗᵢ⋆[ℂ] _).continuous.comp h).mul h

theorem hasCompactSupport_UK {E : Type} [Zero E] [TopologicalSpace E] (f : UK n → E) : HasCompactSupport f :=
  isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)

theorem Fk_int (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) : Integrable (Fk (n := n) lam) (Measure.haar : Measure (UK n)) :=
  (Fk_cont hF lam).integrable_of_hasCompactSupport (hasCompactSupport_UK _)

theorem gram_inv (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) (k : UK n) :
    ContinuousLinearMap.adjoint (Ak lam k) * gramQ lam * Ak lam k = gramQ lam := by
  let L : (EV n lam →L[ℂ] EV n lam) →L[ℂ] (EV n lam →L[ℂ] EV n lam) :=
    (ContinuousLinearMap.mul ℂ _ (ContinuousLinearMap.adjoint (Ak lam k))).comp
      ((ContinuousLinearMap.mul ℂ _).flip (Ak lam k))
  have hL : ∀ X, L X = ContinuousLinearMap.adjoint (Ak lam k) * (X * Ak lam k) := fun X => rfl
  have hF' : ∀ k', ContinuousLinearMap.adjoint (Ak lam k) * (Fk lam k' * Ak lam k)
      = Fk lam (k' * k) := by
    intro k'
    simp only [Fk, Ak_mul hF, ← ContinuousLinearMap.star_eq_adjoint, star_mul, mul_assoc]
  rw [gramQ_def, mul_assoc, ← hL, ← L.integral_comp_comm (Fk_int hF lam)]
  simp only [hL, hF']
  exact integral_mul_right_haar (Fk lam) k

theorem inner_gram (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) (v : EV n lam) :
    ⟪v, gramQ lam v⟫_ℂ = ((∫ k, ‖Ak lam k v‖ ^ 2 ∂(Measure.haar : Measure (UK n)) : ℝ) : ℂ) := by
  rw [gramQ_def, ContinuousLinearMap.integral_apply (Fk_int hF lam),
    ← integral_inner ((Fk_int hF lam).apply_continuousLinearMap v), ← integral_complex_ofReal]
  congr 1
  funext k
  rw [Fk, ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem gram_pos (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) (v : EV n lam) (hv : v ≠ 0) :
    0 < ∫ k, ‖Ak lam k v‖ ^ 2 ∂(Measure.haar : Measure (UK n)) := by
  have hc : Continuous fun k : UK n => ‖Ak lam k v‖ ^ 2 :=
    (((Ak_cont hF lam).clm_apply continuous_const).norm).pow 2
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (hasCompactSupport_UK _)
    (fun _ => sq_nonneg _) ?_
  simp [Ak_one hF, hv]

theorem gram_isPositive (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) : (gramQ (n := n) lam).IsPositive := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, LinearMap.isPositive_iff_complex]
  intro x
  have h : ⟪gramQ lam x, x⟫_ℂ = ((∫ k, ‖Ak lam k x‖ ^ 2 ∂(Measure.haar : Measure (UK n)) : ℝ) : ℂ) := by
    rw [← inner_conj_symm, inner_gram hF, Complex.conj_ofReal]
  have h0 : 0 ≤ ∫ k, ‖Ak lam k x‖ ^ 2 ∂(Measure.haar : Measure (UK n)) :=
    integral_nonneg (fun _ => sq_nonneg _)
  change ((RCLike.re ⟪gramQ lam x, x⟫_ℂ : ℝ) : ℂ) = ⟪gramQ lam x, x⟫_ℂ ∧ 0 ≤ RCLike.re ⟪gramQ lam x, x⟫_ℂ
  rw [h]
  simp [h0]

theorem gram_isUnit (hF : MatrixFrechetDerivativeAtZeroLaws) (lam : Fin n → ℤ) : IsUnit (gramQ (n := n) lam) := by
  have hinj : Function.Injective (gramQ (n := n) lam) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have h1 := inner_gram hF lam v
    rw [hv, inner_zero_right] at h1
    have h3 := gram_pos hF lam v hne
    have h4 : (∫ k, ‖Ak lam k v‖ ^ 2 ∂(Measure.haar : Measure (UK n))) = 0 := by exact_mod_cast h1.symm
    linarith
  have hsurj : Function.Surjective (gramQ (n := n) lam) :=
    LinearMap.injective_iff_surjective.mp hinj
  let e := ContinuousLinearEquiv.ofBijective (gramQ (n := n) lam)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨e.toUnit, ContinuousLinearMap.ext fun _ => rfl⟩

end PositivityTheory.RgBcC.CxeAvg
