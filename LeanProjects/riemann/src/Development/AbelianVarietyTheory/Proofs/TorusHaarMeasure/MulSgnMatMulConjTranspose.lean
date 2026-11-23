import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.MinorRatioNear

noncomputable abbrev sgnMat (r p : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)

theorem sgnMat_mul_self (r p : ℕ) : sgnMat r p * sgnMat r p = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem sgnMat_map_conj (r p : ℕ) : (sgnMat r p).map (starRingEnd ℂ) = sgnMat r p := by
  ext a b
  by_cases h : a = b <;> simp [Matrix.diagonal_apply, h]

theorem mul_sgnMat_mul_conjTranspose {r p : ℕ} {g : Matrix (Fin r) (Fin r) ℂ}
    (h : gᵀ * sgnMat r p * g.map (starRingEnd ℂ) = sgnMat r p) :
    g * sgnMat r p * gᴴ = sgnMat r p := by
  have h1 : gᴴ * sgnMat r p * g = sgnMat r p := by
    have := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.map (starRingEnd ℂ)) h
    simp only [Matrix.map_mul, sgnMat_map_conj] at this
    have e : (g.map (starRingEnd ℂ)).map (starRingEnd ℂ) = g := by ext a b; simp
    rw [e] at this
    exact this
  have h2 : (sgnMat r p * gᴴ * sgnMat r p) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, sgnMat_mul_self]
  have h3 : g * (sgnMat r p * gᴴ * sgnMat r p) = 1 := mul_eq_one_comm.1 h2
  calc g * sgnMat r p * gᴴ = g * (sgnMat r p * gᴴ * sgnMat r p) * sgnMat r p := by
        simp only [Matrix.mul_assoc, sgnMat_mul_self, Matrix.mul_one]
    _ = sgnMat r p := by rw [h3, Matrix.one_mul]

theorem signed_sum_rows {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (h : g * sgnMat r p * gᴴ = sgnMat r p) (v : Fin p → ℂ) :
    ∑ a : Fin r, sgn p a * ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  set R : Matrix (Fin p) (Fin r) ℂ := g.submatrix (Fin.castLE hp) id with hR
  have hRR : R * sgnMat r p * Rᴴ = 1 := by
    have : R * sgnMat r p * Rᴴ =
        (g * sgnMat r p * gᴴ).submatrix (Fin.castLE hp) (Fin.castLE hp) := by
      ext i j
      simp [hR, Matrix.mul_apply]
    rw [this, h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [sgn]
  have key : ((v ᵥ* R) ᵥ* sgnMat r p) ⬝ᵥ star (v ᵥ* R) = v ⬝ᵥ star v := by
    rw [Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
      ← Matrix.mul_assoc, hRR, Matrix.vecMul_one]
  apply Complex.ofReal_injective
  push_cast
  simp only [dotProduct, Matrix.vecMul_diagonal, Pi.star_apply, Complex.star_def] at key
  convert key using 2 with a _ i _
  · rw [mul_comm ((v ᵥ* R) a), mul_assoc, Complex.mul_conj']
  · rw [Complex.mul_conj']

theorem neg_sum_rows {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (h : g * sgnMat r p * gᴴ = sgnMat r p) (v : Fin p → ℂ) :
    ∑ i, ‖v i‖ ^ 2 + ∑ a ∈ Finset.univ.filter (fun a : Fin r => ¬ (a : ℕ) < p),
        ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 =
      ∑ i : Fin p, ‖(v ᵥ* g.submatrix (Fin.castLE hp) (Fin.castLE hp)) i‖ ^ 2 := by
  rw [← signed_sum_rows hp h v,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin r => (a : ℕ) < p), add_assoc,
    ← Finset.sum_add_distrib]
  have e0 : ∑ a ∈ Finset.univ.filter (fun a : Fin r => ¬ (a : ℕ) < p),
      (sgn p a * ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 +
        ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    have := (Finset.mem_filter.1 ha).2
    simp [sgn, this]
  rw [e0, add_zero]
  symm
  refine Finset.sum_bij (fun i _ => Fin.castLE hp i) (fun i _ => by simp)
    (fun i _ j _ hij => Fin.castLE_injective _ hij) (fun a ha => ?_) (fun i _ => ?_)
  · exact ⟨⟨a, (Finset.mem_filter.1 ha).2⟩, Finset.mem_univ _, rfl⟩
  · simp [sgn, Matrix.vecMul, dotProduct]

theorem det_block_ne_zero {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (h : g * sgnMat r p * gᴴ = sgnMat r p) :
    (g.submatrix (Fin.castLE hp) (Fin.castLE hp)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have := neg_sum_rows hp h v
  rw [hv0] at this
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at this
  have h1 : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin r => ¬ (a : ℕ) < p),
      ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h2 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h3 : ∑ i, ‖v i‖ ^ 2 = 0 := by linarith
  apply hv
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).1 h3 i (Finset.mem_univ _)
  simpa using this

theorem norm_entry_le_one {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (h : g * sgnMat r p * gᴴ = sgnMat r p) (i : Fin p) (a : Fin r) :
    ‖((g.submatrix (Fin.castLE hp) (Fin.castLE hp))⁻¹ * g.submatrix (Fin.castLE hp) id) i a‖ ≤ 1 := by
  set A := g.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA
  have hu : IsUnit A.det := (det_block_ne_zero hp h).isUnit
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hu
  by_cases ha : (a : ℕ) < p
  · have : (A⁻¹ * g.submatrix (Fin.castLE hp) id) i a = (A⁻¹ * A) i ⟨a, ha⟩ := rfl
    rw [this, hinv, Matrix.one_apply]
    split_ifs <;> simp
  · have hs := neg_sum_rows hp h (A⁻¹ i)
    have e1 : ∀ j, (A⁻¹ i ᵥ* A) j = (1 : Matrix (Fin p) (Fin p) ℂ) i j := fun j => by
      rw [← hinv]; rfl
    rw [← hA] at hs
    have e2 : ∑ j : Fin p, ‖(A⁻¹ i ᵥ* A) j‖ ^ 2 = 1 := by
      simp only [e1]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Matrix.one_apply_ne hj.symm]
      · simp
    have h2 : 0 ≤ ∑ j, ‖A⁻¹ i j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have h3 : ‖(A⁻¹ i ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin r => ¬ (a : ℕ) < p),
        ‖(A⁻¹ i ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 :=
      Finset.single_le_sum (f := fun a => ‖(A⁻¹ i ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2)
        (fun _ _ => by positivity) (by simpa using ha)
    have h4 : ‖(A⁻¹ i ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 ≤ 1 := by linarith
    exact (sq_le_one_iff₀ (norm_nonneg _)).1 h4

theorem exists_det_near_one (p : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ N : Matrix (Fin p) (Fin p) ℂ,
    (∀ i j, ‖(N - 1) i j‖ < δ) → 1 / 2 ≤ ‖N.det‖ := by
  have hc : Continuous fun N : Fin p → Fin p → ℂ => ‖(Matrix.of N).det‖ :=
    (Continuous.matrix_det (A := fun N : Fin p → Fin p → ℂ => Matrix.of N) continuous_id).norm
  obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.1
    (hc.continuousAt (x := fun i j => (1 : Matrix (Fin p) (Fin p) ℂ) i j)) (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun N hN => ?_⟩
  have := @H (fun i j => N i j) (by
    rw [dist_pi_lt_iff hδ]; intro i
    rw [dist_pi_lt_iff hδ]; intro j
    rw [dist_eq_norm]; exact hN i j)
  have e : (Matrix.of fun i j => (1 : Matrix (Fin p) (Fin p) ℂ) i j).det = 1 := Matrix.det_one
  rw [e, norm_one, Real.dist_eq, abs_lt] at this
  have e' : (Matrix.of fun i j => N i j) = N := rfl
  rw [e'] at this
  linarith [this.1]

theorem exists_block_det_ge {r p : ℕ} (hp : p ≤ r) : ∃ δ : ℝ, 0 < δ ∧
    ∀ g n : Matrix (Fin r) (Fin r) ℂ, g * sgnMat r p * gᴴ = sgnMat r p →
      (∀ a b, ‖(n - 1) a b‖ ≤ δ) →
      ‖(g.submatrix (Fin.castLE hp) (Fin.castLE hp)).det‖ / 2 ≤
        ‖((g * n).submatrix (Fin.castLE hp) (Fin.castLE hp)).det‖ := by
  obtain ⟨δ, hδ, H⟩ := exists_det_near_one p
  refine ⟨δ / (r + 1), by positivity, fun g n h hn => ?_⟩
  set A := g.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA
  set R := g.submatrix (Fin.castLE hp) (id : Fin r → Fin r) with hR
  have hu : IsUnit A.det := (det_block_ne_zero hp h).isUnit
  have e1 : (g * n).submatrix (Fin.castLE hp) (Fin.castLE hp) =
      A * (A⁻¹ * R * n.submatrix id (Fin.castLE hp)) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rfl
  have e2 : R * (1 : Matrix (Fin r) (Fin r) ℂ).submatrix id (Fin.castLE hp) = A := by
    have : R * (1 : Matrix (Fin r) (Fin r) ℂ).submatrix id (Fin.castLE hp) =
        (g * 1).submatrix (Fin.castLE hp) (Fin.castLE hp) := rfl
    rw [this, Matrix.mul_one]
  have e3 : A⁻¹ * R * n.submatrix id (Fin.castLE hp) - 1 =
      A⁻¹ * R * (n - 1).submatrix id (Fin.castLE hp) := by
    have : (n - 1).submatrix id (Fin.castLE hp) = n.submatrix id (Fin.castLE hp) -
        (1 : Matrix (Fin r) (Fin r) ℂ).submatrix id (Fin.castLE hp) := rfl
    rw [this, Matrix.mul_sub, Matrix.mul_assoc A⁻¹ R (Matrix.submatrix 1 _ _), e2,
      Matrix.nonsing_inv_mul _ hu]
  have h1 := H (A⁻¹ * R * n.submatrix id (Fin.castLE hp)) fun i j => by
    rw [e3, Matrix.mul_apply]
    calc ‖∑ a, (A⁻¹ * R) i a * (n - 1).submatrix id (Fin.castLE hp) a j‖
        ≤ ∑ a : Fin r, δ / (r + 1) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          rw [norm_mul]
          calc _ ≤ 1 * (δ / (r + 1)) :=
                mul_le_mul (norm_entry_le_one hp h i a) (hn _ _) (norm_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ < δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_div_assoc, div_lt_iff₀ (by positivity)]
          nlinarith
  rw [e1, Matrix.det_mul, norm_mul]
  nlinarith [norm_nonneg A.det]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_nmat_sub_one_le {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    ‖(mat (nmat X z) τ - 1) a b‖ ≤ ‖z‖ := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  simp only [mat, nmat, Matrix.of_apply]
  by_cases h : b < a
  · rw [dif_pos h, if_neg h.ne', sub_zero]
    exact PiLp.norm_apply_le z _
  · rw [dif_neg h, sub_self, norm_zero]
    exact norm_nonneg _

theorem isometry_of_orth {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (τ : X.Ψ) :
    ((mat x0 τ)⁻¹ * mat x τ) * sgnMat r X.p0 * ((mat x0 τ)⁻¹ * mat x τ)ᴴ = sgnMat r X.p0 := by
  apply mul_sgnMat_mul_conjTranspose
  have hu : IsUnit (mat x0 τ).det := (ExF.det_ne_of_orth X h0 τ).isUnit
  have := FrameDegreeData.gram_mul τ.1 X.Gm (mat x0 τ) ((mat x0 τ)⁻¹ * mat x τ)
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, hx τ, h0 τ] at this
  exact this.symm

theorem dmin_cpt_eq {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X x z) τ i = dmin X.Gm (cpt X x0 z) τ i := by
  unfold dmin
  rw [ExF.mat_cpt, ExF.mat_cpt, FrameDegreeData.gram_mul, FrameDegreeData.gram_mul, hx τ, h0 τ]

theorem minorRatio_near :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ C * (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) := by
  intro r X x0 h0
  set i0 : Fin (r + 1) := ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ with hi0
  obtain ⟨δ, hδ, H⟩ := exists_block_det_ge X.p0_le
  have hc : Continuous fun z : V (nd X) => fun τ : X.Ψ => dmin X.Gm (cpt X x0 z) τ i0 :=
    continuous_pi fun τ => (ExtFPf.cont_dmin X τ i0).comp (FundSetPf.cont_cpt (X := X) (x0 := x0))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V (nd X)) δ).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨δ, ∏ _τ : X.Ψ, (4 * B), hδ, fun x hx z hz => ?_⟩
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun τ _ => by positivity) fun τ _ => ?_
  have hiso := isometry_of_orth X h0 hx τ
  have h1 : ‖dmin X.Gm (cpt X x z) τ i0‖ ≤ B := by
    rw [dmin_cpt_eq X h0 hx]
    exact (norm_le_pi_norm (fun τ : X.Ψ => dmin X.Gm (cpt X x0 z) τ i0) τ).trans
      (hB z (by simpa using hz.le))
  have h2 : ‖lminor ((mat x0 τ)⁻¹ * mat x τ) i0‖ / 2 ≤
      ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x z) τ) i0‖ := by
    rw [ExF.mat_cpt, ← Matrix.mul_assoc]
    exact H _ _ hiso fun a b => (norm_nmat_sub_one_le X z τ a b).trans hz.le
  have h3 : 0 < ‖lminor ((mat x0 τ)⁻¹ * mat x τ) i0‖ :=
    norm_pos_iff.2 (det_block_ne_zero X.p0_le hiso)
  rw [IC.norm_dmin_orth X hx]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
  calc _ ≤ B / (‖lminor ((mat x0 τ)⁻¹ * mat x τ) i0‖ / 2) ^ 2 := by gcongr
    _ = _ := by field_simp; norm_num

end GlobalTheory.MinorRatioNear
