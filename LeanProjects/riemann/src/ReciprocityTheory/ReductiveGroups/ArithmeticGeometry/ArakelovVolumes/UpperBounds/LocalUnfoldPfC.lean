import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

def uL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * (mat b1 τ)⁻¹ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def vL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

theorem cont_uL : Continuous (uL X x1' b1) := by
  unfold uL
  exact continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)

variable {X b1}

theorem mat_uL (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (uL X x1' b1 x) τ = mat x1' τ * (mat b1 τ)⁻¹ * (mat x1' τ)⁻¹ * mat x τ := rfl

private lemma det_mat_ne_zero_of_isOrth {x : Frame X.Ψ r} (ho : IsOrth X x) (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have hg := ho τ
  have e : gram τ.1 X.Gm (mat x τ) =
      (mat x τ).transpose * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hd := congrArg Matrix.det hg
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at hd
  refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
  unfold sgn
  split_ifs <;> norm_num

theorem uL_cpt (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) (z : V (nd X)) (b : Frame X.Ψ r) :
    uL X x1' b1 (rmul (cpt X (rmul x1' b1) z) b) = rmul (cpt X x1' z) b := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have hB := isUnit_iff_ne_zero.mpr (hb1 τ).1
  have e : ∀ x b : Frame X.Ψ r, mat (rmul x b) τ = mat x τ * mat b τ := fun _ _ => rfl
  show mat (uL X x1' b1 (rmul (cpt X (rmul x1' b1) z) b)) τ = mat (rmul (cpt X x1' z) b) τ
  rw [mat_uL]
  simp only [cpt, e, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hB]

theorem vL_uL (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) (x : Frame X.Ψ r) :
    vL X x1' b1 (uL X x1' b1 x) = x := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have hB := isUnit_iff_ne_zero.mpr (hb1 τ).1
  have e : ∀ y : Frame X.Ψ r,
      mat (vL X x1' b1 y) τ = mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat y τ := fun _ => rfl
  show mat (vL X x1' b1 (uL X x1' b1 x)) τ = mat x τ
  rw [e, mat_uL]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.mul_nonsing_inv_cancel_left _ _ hB,
    Matrix.mul_nonsing_inv_cancel_left _ _ hA]

theorem vL_cpt (ho' : IsOrth X x1') (z : V (nd X)) (b : Frame X.Ψ r) :
    vL X x1' b1 (rmul (cpt X x1' z) b) = rmul (cpt X (rmul x1' b1) z) b := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have e : ∀ x b : Frame X.Ψ r, mat (rmul x b) τ = mat x τ * mat b τ := fun _ _ => rfl
  have e2 : ∀ y : Frame X.Ψ r,
      mat (vL X x1' b1 y) τ = mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat y τ := fun _ => rfl
  show mat (vL X x1' b1 (rmul (cpt X x1' z) b)) τ = mat (rmul (cpt X (rmul x1' b1) z) b) τ
  rw [e2]
  simp only [cpt, e, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA]

theorem Tset_eq_pre (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') :
    Tset X (rmul x1' b1) ρ = uL X x1' b1 ⁻¹' (ExtFPf.cell D ∩ D.zOf ⁻¹' Metric.ball 0 ρ) := by
  ext x
  constructor
  · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    rw [uL_cpt ho' hb1]
    obtain ⟨hΔ, hzz, -⟩ := D.uniq z (hO hz) b hb
    exact ⟨⟨OntoS.dom_rmul X (hO hz) hb, hΔ⟩, by rw [hzz]; exact hz⟩
  · rintro ⟨hcell, hzb⟩
    obtain ⟨-, hbm, e⟩ := D.split _ hcell.1 hcell.2
    refine ⟨⟨D.zOf (uL X x1' b1 x), D.bOf (uL X x1' b1 x)⟩, ⟨hzb, hbm⟩, ?_⟩
    simp only
    rw [← vL_cpt (b1 := b1) ho', ← e, vL_uL ho' hb1]

include D in
theorem isOpen_Tset (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') : IsOpen (Tset X (rmul x1' b1) ρ) := by
  rw [Tset_eq_pre D ho' hb1 hO]
  exact (D.hz.continuousOn.isOpen_inter_preimage (ExtFPf.isOpen_cell D) Metric.isOpen_ball).preimage
    (cont_uL X b1)

private lemma lact_lact_eq_lact_mul (γ δ : GL (Fin r) E) (x : Frame X.Ψ r) :
    lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

private lemma lact_one_upper_bounds (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem sat_eq (x1 : Frame X.Ψ r) (ρ : ℝ) :
    {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ, x = lact γ (rmul (cpt X x1 z') b)} =
      ⋃ γ : X.Γ, lact γ.1⁻¹ ⁻¹' Tset X x1 ρ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Tset, Set.mem_image, Set.mem_prod,
    Prod.exists]
  constructor
  · rintro ⟨γ, hγ, b, hb, z', hz', rfl⟩
    refine ⟨⟨γ, hγ⟩, z', b, ⟨hz', hb⟩, ?_⟩
    show _ = lact γ⁻¹ (lact γ _)
    rw [lact_lact_eq_lact_mul, inv_mul_cancel, lact_one_upper_bounds]
  · rintro ⟨⟨γ, hγ⟩, z', b, ⟨hz', hb⟩, h⟩
    refine ⟨γ, hγ, b, hb, z', hz', ?_⟩
    have h' : lact γ (lact γ⁻¹ x) = lact γ (rmul (cpt X x1 z') b) := by
      rw [← h]
    rw [lact_lact_eq_lact_mul, mul_inv_cancel, lact_one_upper_bounds] at h'
    exact h'

include D in
theorem isOpen_sat (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') :
    IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
      x = lact γ (rmul (cpt X (rmul x1' b1) z') b)} := by
  rw [sat_eq]
  refine isOpen_iUnion fun γ => ?_
  have hc : Continuous (fun x : Frame X.Ψ r => lact γ.1⁻¹ x) :=
    continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)
  exact (isOpen_Tset D ho' hb1 hO).preimage hc

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
