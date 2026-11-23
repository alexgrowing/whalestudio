import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SIntEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmDSingleMulVec

noncomputable section

open Matrix MeasureTheory Filter

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
  {u : Fin k → ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {Vp : Type}
  [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
  {μW μN : Measure (Mt k r)} {P x₀ g : Mat k r} {w : H} {a : ℝ}

theorem good_bound {m : H} (hm : TmGood ε σ x₀ w a m) :
    ∃ C : ℝ, ∀ y ∈ UJset ε, ‖coefX σ x₀ w m y‖ ≤ C * frob y ^ (1 - a) := by
  obtain ⟨C, hC⟩ := hm.2 []
  refine ⟨|C|, fun y hy => (hC y hy).trans ?_⟩
  have h1 := tmA_one_le_frob hy (0 : Fin (2 * r + k + 1))
  exact mul_le_mul (le_abs_self C) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
    (Real.rpow_nonneg (by linarith) _) (abs_nonneg C)

theorem per_lin (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN) (hg : g ∈ UH (Hpk k r))
    (hb : S0.bS k r < a - 1) (ξ : Vp) {m m' : H} (hm : TmGood ε σ x₀ w a m)
    (hm' : TmGood ε σ x₀ w a m') (t : ℂ) :
    per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w (m + t • m')) ξ g =
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w m) ξ g +
        t • per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w m') ξ g := by
  obtain ⟨C, hC⟩ := good_bound hm
  obtain ⟨C', hC'⟩ := good_bound hm'
  have i1 := CurveContinuity.int_of_bound hP hB hg ξ a hb _ (CurveContinuity.smooth_contOn hm.1) C hC
  have i2 := CurveContinuity.int_of_bound hP hB hg ξ a hb _ (CurveContinuity.smooth_contOn hm'.1) C' hC'
  unfold per sInt
  rw [← integral_smul]
  refine Eq.trans ?_ (integral_add i1 (i2.smul t))
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [coefX, map_add, map_smul, inner_add_right, inner_smul_right, add_smul, smul_smul,
    Pi.smul_apply]

theorem frame_form (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hg : g ∈ UH (Hpk k r)) :
    IsUnit (g * P⁻¹).det ∧ (g * P⁻¹)ᴴ * Hpk k r * (g * P⁻¹) = Jm ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  refine ⟨by rw [Matrix.det_mul]; exact (TransportGeo.uh_det hg).mul (Matrix.isUnit_nonsing_inv_det P hd),
    ?_⟩
  calc (g * P⁻¹)ᴴ * Hpk k r * (g * P⁻¹) = (P⁻¹)ᴴ * (gᴴ * Hpk k r * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * Pᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by rw [hg', ← hP.2]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]; rfl

theorem mul_inUJ (hP : Formalism.MainNotions.S.IsCayley k r ε P) {y : Mat k r} (hy : y ∈ UH (Hpk k r)) :
    P * y * P⁻¹ ∈ UJset ε := by
  show (P * y * P⁻¹)ᴴ * Jm ε * (P * y * P⁻¹) = Jm ε
  have h := (frame_form hP hy).2
  rw [← hP.2] at h
  refine Eq.trans ?_ h
  show (P * y * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * y * P⁻¹) = _
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem per_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hx₀ : x₀ ∈ UJset ε)
    (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN) (hg : g ∈ UH (Hpk k r))
    (hb : S0.bS k r < a - 1) (ξ : Vp) {Y : Mat k r} (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) (m : D)
    (hm : TmGood ε σ x₀ w a (m : H))
    (hm' : TmGood ε σ x₀ w a ((actM E ((g * P⁻¹)⁻¹ * Y * (g * P⁻¹)) m : D) : H)) :
    HasDerivAt (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w (m : H)) ξ
        (NormedSpace.exp ((t : ℂ) • Y) * g))
      (per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
        (coefX σ x₀ w ((actM E ((g * P⁻¹)⁻¹ * Y * (g * P⁻¹)) m : D) : H)) ξ g) 0 := by
  obtain ⟨hR, hJ⟩ := frame_form hP hg
  set R := g * P⁻¹ with hRd
  have hX : inG ε (R⁻¹ * Y * R) := by
    have e1 : Jm ε * (R⁻¹ * Y * R) = Rᴴ * (Hpk k r * Y) * R := by
      rw [← hJ]; simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hR]
    have e2 : (R⁻¹ * Y * R)ᴴ * Jm ε = Rᴴ * (Yᴴ * Hpk k r) * R := by
      have h2 : (R⁻¹)ᴴ * Rᴴ = 1 := by
        rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hR, conjTranspose_one]
      rw [← hJ]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (R⁻¹)ᴴ, h2, Matrix.one_mul]
    show (R⁻¹ * Y * R)ᴴ * Jm ε + Jm ε * (R⁻¹ * Y * R) = 0
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hY, Matrix.mul_zero, Matrix.zero_mul]
  have hRd' : ∀ y ∈ UJset ε, Formalism.REAL.Rd (R⁻¹ * Y * R) (coefX σ x₀ w (m : H)) y =
      coefX σ x₀ w ((actM E (R⁻¹ * Y * R) m : D) : H) y := fun y hy =>
    tmB_rd_coef hσ hD (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hy) hX w m
  obtain ⟨C, hC⟩ := good_bound hm
  obtain ⟨C', hC'⟩ := good_bound hm'
  have h := (CurveContinuity.deriv_int hP hB hg ξ a hb _ hm.1 C hC _ hX C'
    (fun y hy => by rw [hRd' y hy]; exact hC' y hy)).2
  refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
  · have e : NormedSpace.exp ((t : ℂ) • (R⁻¹ * Y * R)) = R⁻¹ * NormedSpace.exp ((t : ℂ) • Y) * R := by
      rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det R).mpr hR), Matrix.mul_smul,
        Matrix.smul_mul]
    simp only [per, sInt, e]
    congr 1
    funext p
    congr 2
    calc _ = P * (Matrix.of p.1 * Matrix.of p.2) * (NormedSpace.exp ((t : ℂ) • Y) * R) := by
          rw [hRd]; simp only [Matrix.mul_assoc]
      _ = P * (Matrix.of p.1 * Matrix.of p.2) * (R * (R⁻¹ * (NormedSpace.exp ((t : ℂ) • Y) * R))) := by
          rw [Matrix.mul_nonsing_inv_cancel_left _ _ hR]
      _ = _ := by
          rw [← Matrix.mul_assoc R⁻¹]
          generalize R⁻¹ * NormedSpace.exp ((t : ℂ) • Y) * R = A
          rw [hRd]; simp only [Matrix.mul_assoc]
  · unfold per sInt
    refine integral_congr_ae ?_
    filter_upwards [CurveContinuity.ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2] with p hp
    rw [hRd' _ (mul_inUJ hP (TransportGeo.uh_mul (TransportGeo.uh_mul hp.1.1 hp.2.1) hg))]

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
