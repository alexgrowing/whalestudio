import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsMinNormTensorOfIsClosedTensorSLOrbitStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MinNormTensorStabilizerConjTransposeInvariantStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealTranslateIsMinNormTensorInOrbitStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorSLOrbitMapProperOfIsClosedStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SiegelCoverStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BorelHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebraStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem finite_bdd_denominator_vectors {κ : Type} [Fintype κ] (D : ℕ) (hD : 0 < D) (B : ℝ) :
    {w : κ → ℚ | (∀ k, ∃ z : ℤ, (D : ℚ) * w k = z) ∧ nsq (fun k => ((w k : ℚ) : ℂ)) ≤ B}.Finite := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge ((D : ℝ) * (B + 1))
  have hDq : (D : ℚ) ≠ 0 := by positivity
  have hfin : ((fun z : ℤ => (z : ℚ) / D) '' (Set.Icc (-(N : ℤ)) N)).Finite :=
    (Set.finite_Icc _ _).image _
  refine (Set.Finite.pi' (fun _ : κ => hfin)).subset ?_
  rintro w ⟨hw, hB⟩ k
  obtain ⟨z, hz⟩ := hw k
  refine ⟨z, ?_, ?_⟩
  · have h1 : ‖((w k : ℚ) : ℂ)‖ ^ 2 ≤ B := by
      refine le_trans ?_ hB
      exact Finset.single_le_sum (f := fun k => ‖((w k : ℚ) : ℂ)‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ k)
    have h2 : ‖((w k : ℚ) : ℂ)‖ = |(w k : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    rw [h2] at h1
    have h3 : |(w k : ℝ)| ≤ B + 1 := by nlinarith [abs_nonneg (w k : ℝ), sq_nonneg (|(w k : ℝ)| - 1)]
    have h4 : (z : ℝ) = D * (w k : ℝ) := by exact_mod_cast hz.symm
    have h5 : |(z : ℝ)| ≤ N := by
      rw [h4, abs_mul, Nat.abs_cast]
      exact le_trans (mul_le_mul_of_nonneg_left h3 (by positivity)) hN
    have h6 : |z| ≤ (N : ℤ) := by exact_mod_cast h5
    exact abs_le.mp h6
  · simp only
    rw [← hz]; field_simp

theorem finite_integral_classes_closed_orbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) → ∀ D : ℕ, 0 < D → ∃ Z : Finset (TIdx ι d → ℚ), ∀ h : Matrix ι ι ℚ, h.det = 1 → (∀ k, ∃ z : ℤ, (D : ℚ) * act d t h k = z) → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ act d t (h * γ.map (Int.cast : ℤ → ℚ)) ∈ Z := by
  intro ι _ _ m d t hcl D hD
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hC := (GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).2 m d
  have hQ := (GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℚ).2 m d
  set tC : TIdx ι d → ℂ := fun k => ((t k : ℚ) : ℂ) with htC
  have htR : (fun k => (((t k : ℚ) : ℝ) : ℂ)) = tC := by
    funext k; simp [htC]
  obtain ⟨g, hg, hmin⟩ := GlobalTheory.T.exists_real_translate_isMinNormTensorInOrbit ι m d (fun k => ((t k : ℚ) : ℝ))
    (by rw [htR]; exact GlobalTheory.T.exists_minNormTensor_of_isClosed_tensorSLOrbit ι m d tC hcl)
  rw [htR] at hmin
  have hmap : ∀ x y : Matrix ι ι ℝ, (x * y).map (fun r : ℝ => (r : ℂ)) =
      x.map (fun r : ℝ => (r : ℂ)) * y.map (fun r : ℝ => (r : ℂ)) := fun x y =>
    Matrix.map_mul (f := Complex.ofRealHom)
  have hgg : g * g.adjugate = 1 := by rw [mul_adjugate, hg, one_smul]
  set gC : Matrix ι ι ℂ := g.map (fun r : ℝ => (r : ℂ)) with hgC
  have hgCd : gC.det = 1 := by
    have := (RingHom.map_det Complex.ofRealHom g)
    rw [hg, map_one] at this
    exact this.symm
  have hgCadj : gC * gC.adjugate = 1 := by rw [mul_adjugate, hgCd, one_smul]
  set v := act d tC gC with hv
  have horb : orb d v = orb d tC := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨gC * y, by rw [det_mul, hgCd, hy, one_mul], by rw [(hC tC).2.1]⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨gC.adjugate * y, by rw [det_mul, det_adjugate, hgCd, hy, one_pow, one_mul], ?_⟩
      rw [hv, ← (hC tC).2.1, ← mul_assoc, hgCadj, one_mul]
  obtain ⟨C, hSieg⟩ := GlobalTheory.T.exists_siegel_decomposition_mul_int_matrix_of_det_eq_one ι
  obtain ⟨B, hB⟩ := GlobalTheory.T.nsq_act_le_of_isSiegel_of_entries_zero_or_ge ι m d v (GlobalTheory.T.tensorSLOrbit_map_proper_of_isClosed ι m d v (horb ▸ hcl))
    (GlobalTheory.T.minNormTensor_stabilizer_conjTranspose_invariant ι m d v hmin) C (1 / D) (by positivity)
  refine ⟨(finite_bdd_denominator_vectors (κ := TIdx ι d) D hD B).toFinset, ?_⟩
  intro h hh hint
  have hhR : (h.map (fun q : ℚ => (q : ℝ))).det = 1 := by
    have := (RingHom.map_det (Rat.castHom ℝ) h)
    rw [hh, map_one] at this
    exact this.symm
  obtain ⟨γ, hγ, k, a, n, hS, hkan⟩ := hSieg (g.adjugate * h.map (fun q : ℚ => (q : ℝ)))
    (by rw [det_mul, det_adjugate, hg, hhR, one_pow, one_mul])
  refine ⟨γ, hγ, ?_⟩
  set w := act d t (h * γ.map (Int.cast : ℤ → ℚ)) with hw
  have hwint : ∀ j, ∃ z : ℤ, (D : ℚ) * w j = z := by
    intro j
    have h1 := (hQ ((D : ℚ) • act d t h)).2.2.2.1 (Int.castRingHom ℚ).range
      (γ.map (Int.cast : ℤ → ℚ)) (fun k => by
        obtain ⟨z, hz⟩ := hint k
        exact ⟨z, hz.symm⟩) (fun i j => ⟨γ i j, rfl⟩) j
    rw [(hQ _).2.2.2.2.1, ← (hQ t).2.1] at h1
    obtain ⟨z, hz⟩ := h1
    exact ⟨z, hz.symm⟩
  have hact : act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) = fun j => ((w j : ℚ) : ℂ) := by
    rw [← hkan, hv, ← (hC tC).2.1, hgC, ← hmap, ← mul_assoc, ← mul_assoc, hgg, one_mul]
    have h2 := (hQ t).2.2.2.2.2 ℂ (Rat.castHom ℂ) (h * γ.map (Int.cast : ℤ → ℚ))
    have h3 : (h.map (fun q : ℚ => (q : ℝ)) * γ.map (Int.cast : ℤ → ℝ)).map (fun r : ℝ => (r : ℂ)) =
        (h * γ.map (Int.cast : ℤ → ℚ)).map (Rat.castHom ℂ) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [h3]
    exact h2
  rw [Set.Finite.mem_toFinset]
  refine ⟨hwint, ?_⟩
  rw [← hact]
  refine hB k a n hS ?_
  intro j
  rw [hact]
  obtain ⟨z, hz⟩ := hwint j
  by_cases hz0 : z = 0
  · left
    have : w j = 0 := by
      rw [hz0] at hz
      have hDq : (D : ℚ) ≠ 0 := by positivity
      simpa [hD.ne'] using hz
    simp [this]
  · right
    have h2 : ‖((w j : ℚ) : ℂ)‖ = |(w j : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    have h4 : (z : ℝ) = D * (w j : ℝ) := by exact_mod_cast hz.symm
    have h5 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
    show 1 / (D : ℝ) ≤ ‖((w j : ℚ) : ℂ)‖
    rw [h2, div_le_iff₀ (by positivity)]
    rw [h4, abs_mul, Nat.abs_cast] at h5
    linarith

end GlobalTheory.ClassFin
