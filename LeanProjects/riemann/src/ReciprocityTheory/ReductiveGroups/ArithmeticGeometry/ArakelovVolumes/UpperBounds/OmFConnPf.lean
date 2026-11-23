import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OFC

open NumberField Complex Matrix Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def isW (i : Fin (nd X)) : Prop :=
  X.p0 ≤ (((Fintype.equivFin (Ent X)).symm i).2.1.1 : ℕ) ∧ (((Fintype.equivFin (Ent X)).symm i).2.1.2 : ℕ) < X.p0

instance (i : Fin (nd X)) : Decidable (isW X i) := by unfold isW; infer_instance

def S1 (t : ℝ) (z : V (nd X)) : V (nd X) := WithLp.toLp 2 fun i => if isW X i then (t : ℂ) * z i else z i

def S2 (t : ℝ) (z : V (nd X)) : V (nd X) := WithLp.toLp 2 fun i => if isW X i then 0 else (t : ℂ) * z i

theorem scaledWm_linear (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Wm X (S1 X t z) τ = (t : ℂ) • ExF.Wm X z τ := by
  ext m c
  have hc := c.isLt
  have hlt : Fin.castLE X.p0_le c < ExF.qI X m := by
    rw [Fin.lt_def]
    simp only [Fin.coe_castLE, ExF.qI]
    omega
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S1, dif_pos hlt]
  rw [if_pos]
  simp only [isW, Equiv.symm_apply_apply, ExF.qI, Fin.coe_castLE]
  omega

theorem unipotentFrame_scaling_invariant (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.n1 X (S1 X t z) τ = ExF.n1 X z τ := by
  ext a b
  have ha := a.isLt
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S1]
  split_ifs with h1 h2 <;>
    first
    | rfl
    | (exfalso
       simp only [isW, Equiv.symm_apply_apply, Fin.coe_castLE] at *
       omega)

theorem retractedWm_eq_zero (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Wm X (S2 X t z) τ = 0 := by
  ext m c
  have hc := c.isLt
  have hlt : Fin.castLE X.p0_le c < ExF.qI X m := by
    rw [Fin.lt_def]
    simp only [Fin.coe_castLE, ExF.qI]
    omega
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S2, dif_pos hlt, Matrix.zero_apply]
  rw [if_pos]
  simp only [isW, Equiv.symm_apply_apply, ExF.qI, Fin.coe_castLE]
  omega

theorem scaledZt_linear (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Zt X (S1 X t z) τ = (t : ℂ) • ExF.Zt X z τ := by
  simp only [ExF.Zt, scaledWm_linear, unipotentFrame_scaling_invariant, Matrix.smul_mul, Matrix.transpose_smul]

theorem retractedZt_eq_zero (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Zt X (S2 X t z) τ = 0 := by
  simp only [ExF.Zt, retractedWm_eq_zero, Matrix.zero_mul, Matrix.transpose_zero]

theorem S1_mem_OmF (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : S1 X t z ∈ OmF X x0 := by
  rw [ExF.mem_OmF_iff X x0 ho] at hz ⊢
  intro τ
  have hA := hz τ
  have heq : ExF.Am X (S1 X t z) τ =
      ((1 - t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) + ((t ^ 2 : ℝ) : ℂ) • ExF.Am X z τ := by
    simp only [ExF.Am, scaledZt_linear, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.star_def, Complex.conj_ofReal]
    have e1 : ((1 - t ^ 2 : ℝ) : ℂ) = 1 - (t : ℂ) * t := by
      push_cast
      ring
    have e2 : ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) * t := by
      push_cast
      ring
    rw [e1, e2, sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  rcases ht0.lt_or_eq with htpos | rfl
  · have h2 : (0 : ℂ) < ((t ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast pow_pos htpos 2
    have h1 : (0 : ℂ) ≤ ((1 - t ^ 2 : ℝ) : ℂ) := by
      have : t ^ 2 ≤ 1 := by nlinarith
      exact_mod_cast sub_nonneg.2 this
    exact (hA.smul h2).posSemidef_add ((Matrix.PosSemidef.one).smul h1)
  · simpa using Matrix.PosDef.one

theorem radialRetraction_mem_chart (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (t : ℝ) : S2 X t z ∈ OmF X x0 := by
  rw [ExF.mem_OmF_iff X x0 ho]
  intro τ
  simp only [ExF.Am, retractedZt_eq_zero, Matrix.zero_mul, sub_zero]
  exact Matrix.PosDef.one

theorem continuous_linearScaling (z : V (nd X)) : Continuous fun t : ℝ => S1 X t z := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  by_cases h : isW X i
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    fun_prop

theorem continuous_radialRetraction (z : V (nd X)) : Continuous fun t : ℝ => S2 X t z := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  by_cases h : isW X i
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    fun_prop

theorem linearScaling_zero_eq_retraction (z : V (nd X)) : S1 X 0 z = S2 X 1 z := by
  ext i
  simp only [S1, S2, WithLp.ofLp_toLp, PiLp.toLp_apply]
  split_ifs <;> simp

theorem radialRetraction_at_zero (z : V (nd X)) : S2 X 0 z = 0 := by
  ext i
  simp only [S2, WithLp.ofLp_toLp, PiLp.toLp_apply]
  split_ifs <;> simp

theorem linearScaling_at_one (z : V (nd X)) : S1 X 1 z = z := by
  ext i
  simp only [S1, WithLp.ofLp_toLp, PiLp.toLp_apply]
  split_ifs <;> simp

end

theorem omFConn_of_cm {E : Type} [Field E] [NumberField E] [IsCMField E] : OmFConnStatement (E := E) := by
  intro r X x0 ho
  refine isPreconnected_of_forall 0 fun y hy => ?_
  refine ⟨(fun t => S2 X t y) '' Set.Icc 0 1 ∪ (fun t => S1 X t y) '' Set.Icc 0 1, ?_, ?_, ?_, ?_⟩
  · rintro w (⟨t, -, rfl⟩ | ⟨t, ⟨ht0, ht1⟩, rfl⟩)
    · exact radialRetraction_mem_chart X x0 ho y t
    · exact S1_mem_OmF X x0 ho hy ht0 ht1
  · exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, radialRetraction_at_zero X y⟩
  · exact Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, linearScaling_at_one X y⟩
  · refine IsPreconnected.union (S2 X 1 y) ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
      ⟨0, ⟨le_rfl, zero_le_one⟩, linearScaling_zero_eq_retraction X y⟩ ?_ ?_
    · exact isPreconnected_Icc.image _ (continuous_radialRetraction X y).continuousOn
    · exact isPreconnected_Icc.image _ (continuous_linearScaling X y).continuousOn

end ReciprocityTheory.ChartRestriction.G.AR.Up.OFC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem OmFConnStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    OmFConnStatement (E := E) :=
  OFC.omFConn_of_cm

end ReciprocityTheory.ChartRestriction.G.AR.Up
