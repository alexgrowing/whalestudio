import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric Polynomial

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}

theorem lminor_one (k : Fin (r + 1)) : lminor (1 : Matrix (Fin r) (Fin r) ℂ) k = 1 := by
  unfold lminor
  rw [Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]

theorem orthogonalFrame_delta_eq_one (hx0 : IsOrth X x0) : DeltaF X x0 x0 = 1 := by
  unfold DeltaF
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
  have h : Mx X x0 x0 τ = 1 := by
    unfold Mx
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (orthogonalFrame_det_ne_zero (X := X) (x0 := x0) hx0 τ))
  rw [h, lminor_one]

def linePoly (x v : Frame X.Ψ r) : ℂ[X] :=
  ∏ τ, ∏ k : Fin (r + 1),
    (((Mx X x0 x τ).map C + (Polynomial.X : ℂ[X]) • ((mat x0 τ)⁻¹ * mat v τ).map C).submatrix
      (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det

theorem linePoly_eval (x v : Frame X.Ψ r) (t : ℂ) :
    (linePoly (x0 := x0) x v).eval t = DeltaF X x0 (x + t • v) := by
  unfold linePoly DeltaF lminor
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Mx, mat, Matrix.mul_apply, Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_left_comm,
    Polynomial.eval_finset_sum]

theorem dense_delta (hx0 : IsOrth X x0) (x : Frame X.Ψ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ ball x ε, DeltaF X x0 y ≠ 0 := by
  classical
  set w : Frame X.Ψ r := x0 - x
  set P := linePoly (x0 := x0) x w
  have hP1 : P.eval 1 = 1 := by
    rw [linePoly_eval, one_smul, add_sub_cancel, orthogonalFrame_delta_eq_one hx0]
  have hP0 : P ≠ 0 := by
    rintro h
    rw [h, Polynomial.eval_zero] at hP1
    exact zero_ne_one hP1
  set δ : ℝ := ε / (‖w‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hinf : ((fun s : ℝ => (s : ℂ)) '' Set.Ioo 0 δ).Infinite :=
    (Set.Ioo_infinite hδ).image (fun a _ b _ h => Complex.ofReal_injective h)
  obtain ⟨c, hc, hcP⟩ := (hinf.diff (Polynomial.finite_setOf_isRoot hP0)).nonempty
  obtain ⟨s, hs, rfl⟩ := hc
  refine ⟨x + (s : ℂ) • w, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs.1]
    calc s * ‖w‖ ≤ δ * ‖w‖ := by gcongr; exact hs.2.le
      _ < δ * (‖w‖ + 1) := by gcongr; linarith
      _ = ε := by
        have : (‖w‖ + 1) ≠ 0 := by positivity
        simp only [δ]
        field_simp
  · rw [← linePoly_eval]
    exact hcP

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem lu_holds : LUStatement (E := E) := by
  intro r X x0 hx0
  refine ⟨DeltaF X x0, zF X x0, bF X x0, Delta_diff (X := X) (x0 := x0),
    fun x _ ε hε => dense_delta (X := X) (x0 := x0) hx0 x ε hε,
    zF_diffOn (X := X) (x0 := x0), bF_diffOn (X := X) (x0 := x0),
    fun x hx hΔ => ⟨zF_mem (X := X) (x0 := x0) hx0 hx hΔ, bF_mem (X := X) (x0 := x0) hx hΔ,
      split_eq (X := X) (x0 := x0) hx0 x⟩,
    fun z _ b hb => uniq_all (X := X) (x0 := x0) hx0 hb⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
