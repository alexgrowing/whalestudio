import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockModelPosFrameBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricBoundPuncturedPolydisc
open Matrix Filter Topology
open scoped ComplexOrder

open Complex Metric GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.PoincareBounds GlobalTheory.CurvInterp in
theorem UpperTheory.poincare_derivative_bound :
    ∀ (e n k : ℕ) (hk : k ≤ n) (φ : (Fin e → ℂ) → Fin n → ℂ) (z : Fin e → ℂ) (δ : ℝ), 0 < δ → DifferentiableOn ℂ φ (Metric.ball z δ) → (∀ w ∈ Metric.ball z δ, φ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured hk 1) → ∀ w : Fin e → ℂ, GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram k (φ z)) (fderiv ℂ φ z w) ≤ ((n : ℝ) + 1) * (8 * Real.pi) * (‖w‖ / δ) := by
  intro e n k hk φ z δ₀ hδ₀pos hφd hφP w
  classical
  set M := ‖w‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  rcases hM0.eq_or_lt with hM | hMpos
  · have hw : w = 0 := norm_eq_zero.1 hM.symm
    subst hw
    simp only [map_zero, gnorm_zero]
    positivity
  set δ := δ₀ / M with hδdef
  have hδ : 0 < δ := div_pos hδ₀pos hMpos
  have hδM : δ * M = δ₀ := div_mul_cancel₀ _ hMpos.ne'
  let γ : ℂ → Fin e → ℂ := fun ζ => z + ζ • w
  have hγ0 : γ 0 = z := by simp [γ]
  have hγd : HasDerivAt γ w 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add z
    simpa [γ] using h
  have hγdiff : Differentiable ℂ γ := by
    simp only [γ]; fun_prop
  have hmaps : Set.MapsTo γ (ball 0 δ) (ball z δ₀) := by
    intro ζ hζ
    have hζ' : ‖ζ‖ < δ := mem_ball_zero_iff.1 hζ
    rw [mem_ball, dist_eq_norm]
    have e1 : γ ζ - z = ζ • w := by simp [γ]
    rw [e1, norm_smul, ← hδM]
    exact mul_lt_mul_of_pos_right hζ' hMpos
  have hzB : z ∈ ball z δ₀ := mem_ball_self hδ₀pos
  have hzP : φ z ∈ punctured hk 1 := hφP z hzB
  have hφz : DifferentiableAt ℂ φ z := (hφd z hzB).differentiableAt (isOpen_ball.mem_nhds hzB)
  have hcomp : HasDerivAt (fun ζ => φ (γ ζ)) (fderiv ℂ φ z w) 0 := by
    have h : HasFDerivAt φ (fderiv ℂ φ z) (γ 0) := by rw [hγ0]; exact hφz.hasFDerivAt
    exact h.comp_hasDerivAt 0 hγd
  have hFd : ∀ i, DifferentiableOn ℂ (fun ζ => φ (γ ζ) i) (ball 0 δ) := fun i =>
    differentiableOn_pi.1 (hφd.comp hγdiff.differentiableOn hmaps) i
  have hF1 : ∀ i, ∀ ζ ∈ ball (0 : ℂ) δ, ‖φ (γ ζ) i‖ < 1 := fun i ζ hζ => (hφP _ (hmaps hζ)).1 i
  have hder : ∀ i, deriv (fun ζ => φ (γ ζ) i) 0 = fderiv ℂ φ z w i := fun i =>
    (hasDerivAt_pi.1 hcomp i).deriv
  have hF0 : ∀ i, φ (γ 0) i = φ z i := fun i => by rw [hγ0]
  set v := fderiv ℂ φ z w with hv
  have hδinv : 1 / δ = M / δ₀ := by rw [hδdef]; field_simp
  set K := 8 * Real.pi / δ₀ * M with hK
  have hK0 : 0 ≤ K := by positivity
  have hvall : ∀ i, ‖v i‖ ≤ K := by
    intro i
    have h := norm_deriv_le_of_norm_lt_one hδ (hFd i) (hF1 i)
    rw [hder i] at h
    calc ‖v i‖ ≤ 2 / δ := h
      _ = 2 * (M / δ₀) := by rw [← hδinv]; ring
      _ ≤ K := by
        rw [hK, mul_div_assoc', div_mul_eq_mul_div]
        gcongr
        · linarith [Real.pi_gt_three]
  have hvbr : ∀ i : Fin n, i.val < k → ‖v i‖ ≤ K * (‖φ z i‖ * tlog (φ z i)) := by
    intro i hi
    have hne : ∀ ζ ∈ ball (0 : ℂ) δ, φ (γ ζ) i ≠ 0 := fun ζ hζ =>
      (hφP _ (hmaps hζ)).2 ⟨i.val, hi⟩
    have h := norm_deriv_le_of_punctured hδ (hFd i) hne (hF1 i)
    rw [hder i, hF0 i] at h
    have hl : -Real.log ‖φ z i‖ = 2 * Real.pi * tlog (φ z i) := by
      simp only [tlog]; field_simp
    calc ‖v i‖ ≤ 4 * (-Real.log ‖φ z i‖) * ‖φ z i‖ / δ := h
      _ = K * (‖φ z i‖ * tlog (φ z i)) := by
        rw [hl, div_eq_mul_one_div, hδinv, hK]; field_simp; ring
  have hterm : ∀ i, pdiag k (φ z) i * ‖v i‖ ^ 2 ≤ K ^ 2 := by
    intro i
    unfold pdiag
    split_ifs with hi
    · have hp0 : φ z i ≠ 0 := hzP.2 ⟨i.val, hi⟩
      obtain ⟨hp, -⟩ := norm_mul_tlog_lt hp0 (hzP.1 i)
      have h := hvbr i hi
      have h2 : ‖v i‖ ^ 2 ≤ (K * (‖φ z i‖ * tlog (φ z i))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      have e1 : ‖φ z i‖ ^ 2 * tlog (φ z i) ^ 2 = (‖φ z i‖ * tlog (φ z i)) ^ 2 := by ring
      rw [e1, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg K, sq_nonneg (‖φ z i‖ * tlog (φ z i))]
    · have h2 : ‖v i‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hvall i) 2
      nlinarith
  have hsum : gnorm (poincareGram k (φ z)) v ^ 2 ≤ ((n + 1) * K) ^ 2 := by
    rw [poincareGram_eq, gnorm_diag_sq _ (pdiag_nonneg k (φ z))]
    calc ∑ i, pdiag k (φ z) i * ‖v i‖ ^ 2 ≤ ∑ _i : Fin n, K ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = n * K ^ 2 := by simp
      _ ≤ ((n + 1) * K) ^ 2 := by
        have : (n : ℝ) ≤ (n + 1) ^ 2 := by nlinarith
        nlinarith [sq_nonneg K]
  have hfin := (pow_le_pow_iff_left₀ (gnorm_nonneg _ _) (by positivity) two_ne_zero).1 hsum
  calc gnorm (poincareGram k (φ z)) v ≤ (n + 1) * K := hfin
    _ = ((n : ℝ) + 1) * (8 * Real.pi) * (M / δ₀) := by rw [hK]; ring
