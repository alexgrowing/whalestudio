import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem quad_eq (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Fin a → Cinf E) :
    quad p x = ∑ w : InfinitePlace E, ∑ j, ∑ i, (x i w * p i j w * star (x j w)).re := by
  simp only [quad, dotProduct, vecMul, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, Complex.re_sum, Finset.sum_mul]

private theorem qf_eq (x : Fin a → Cinf E) :
    qf x = ∑ w : InfinitePlace E, ((x ⬝ᵥ star x) w).re := by
  rw [qf, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dotProduct, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem UpperTheory.geometric_side_quadraticForm_identity :
    QfFacts := by
  intro E _ _ a
  refine ⟨fun x => ?_, fun p p' c x => ⟨?_, ?_⟩, fun h x => ?_, fun c x => ?_, fun p x => ?_, fun x => ⟨?_, ?_⟩⟩
  · rw [qf_eq, quad, vecMul_one]
  · simp only [quad_eq, Matrix.add_apply, Pi.add_apply, mul_add, add_mul, Complex.add_re, Finset.sum_add_distrib]
  · simp only [quad_eq, Matrix.smul_apply, Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, Complex.smul_re, smul_eq_mul]
  · rw [qf_eq, quad, star_vecMul, dotProduct_mulVec, vecMul_vecMul]
    rfl
  · simp only [qf, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  · have hp : ∀ i j w, ‖p i j w‖ ≤ ‖toL p‖ := fun i j w =>
      ((norm_le_pi_norm (toL p i j) w).trans (norm_le_pi_norm (toL p i) j)).trans (norm_le_pi_norm (toL p) i)
    have key : ∀ w j i, |(x i w * p i j w * star (x j w)).re| ≤ ‖toL p‖ / 2 * (‖x i w‖ ^ 2 + ‖x j w‖ ^ 2) := by
      intro w j i
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, norm_star]
      have h1 := hp i j w
      have h2 := norm_nonneg (p i j w)
      have h3 := mul_nonneg (norm_nonneg (x i w)) (norm_nonneg (x j w))
      have h4 := mul_le_mul_of_nonneg_left h1 h3
      have h5 := mul_nonneg (h2.trans h1) (sq_nonneg (‖x i w‖ - ‖x j w‖))
      nlinarith
    rw [quad_eq, qf, Finset.sum_comm (f := fun i w => ‖x i w‖ ^ 2), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    calc _ ≤ ∑ j, ∑ i, ‖toL p‖ / 2 * (‖x i w‖ ^ 2 + ‖x j w‖ ^ 2) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => key w j i))
      _ = _ := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  · have h0 := qf_nonneg x
    have h : ‖x‖ ≤ √(qf x) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => Real.le_sqrt_of_sq_le ?_
      calc ‖x i w‖ ^ 2 ≤ ∑ w, ‖x i w‖ ^ 2 :=
            Finset.single_le_sum (f := fun w => ‖x i w‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w)
        _ ≤ qf x := Finset.single_le_sum (f := fun i => ∑ w, ‖x i w‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖x‖ ^ 2 ≤ √(qf x) ^ 2 := by gcongr
      _ = qf x := Real.sq_sqrt h0
  · calc qf x ≤ ∑ _i : Fin a, ∑ _w : InfinitePlace E, ‖x‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun w _ => ?_
          have := (norm_le_pi_norm (x i) w).trans (norm_le_pi_norm x i)
          gcongr
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
