import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.KB.WhittakerCocycle

theorem posDef_of_sphere {N : ℕ} {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.IsHermitian)
    (h : ∀ v : Fin N → ℂ, ‖v‖ = 1 → 0 < (star v ⬝ᵥ (M *ᵥ v)).re) : M.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hM, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx' : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set u : Fin N → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hr.ne']
  have key : star x ⬝ᵥ (M *ᵥ x) = ((‖x‖ ^ 2 : ℝ) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [hu, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    field_simp
  rw [RCLike.pos_iff]
  refine ⟨?_, hM.im_star_dotProduct_mulVec_self x⟩
  rw [key]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
  exact mul_pos (by positivity) (h u hu1)

theorem isOpen_posW {L : Type} [Field L] [NumberField L] {N : ℕ} (w : InfinitePlace L) :
    IsOpen {h : HS L N | (mat h w).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro h0 h0p
  have hm : Continuous fun z : HS L N × (Fin N → ℂ) => mat z.1 w := by
    show Continuous fun z : HS L N × (Fin N → ℂ) => (z.1.1 w : Matrix (Fin N) (Fin N) ℂ)
    exact (continuous_apply w).comp (continuous_subtype_val.comp continuous_fst)
  have hg : Continuous fun z : HS L N × (Fin N → ℂ) => (star z.2 ⬝ᵥ (mat z.1 w *ᵥ z.2)).re :=
    Complex.continuous_re.comp ((continuous_snd.star).dotProduct (hm.matrix_mulVec continuous_snd))
  have hK : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1) := isCompact_sphere 0 1
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := h0)
    (P := fun h v => 0 < (star v ⬝ᵥ (mat h w *ᵥ v)).re) (fun v hv => by
      have hv0 : v ≠ 0 := by
        rintro rfl
        simp at hv
      have hpos : 0 < (star v ⬝ᵥ (mat h0 w *ᵥ v)).re := by
        have := (show (mat h0 w).PosDef from h0p).re_dotProduct_pos hv0
        simpa using this
      exact (isOpen_lt continuous_const hg).mem_nhds hpos)
  filter_upwards [hev] with h hh
  exact posDef_of_sphere (mat_herm h w) fun v hv => hh v (by simpa using hv)

theorem pos_open_convex (L : Type) [Field L] [NumberField L] (N : ℕ) :
    IsOpen (Pos L N) ∧ Convex ℝ (Pos L N) := by
  refine ⟨?_, ?_⟩
  · have : Pos L N = ⋂ w, {h : HS L N | (mat h w).PosDef} := by
      ext h
      simp [Pos]
    rw [this]
    exact isOpen_iInter_of_finite fun w => isOpen_posW w
  · intro x hx y hy a b ha hb hab w
    show (mat (a • x + b • y) w).PosDef
    rw [mat_add, mat_smul, mat_smul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      simpa using hy w
    · exact ((hx w).smul ha').add_posSemidef ((hy w).posSemidef.smul hb)

theorem actL_scal {L : Type} [Field L] [NumberField L] {N : ℕ} (s : InfinitePlace L → ℂˣ)
    (hs : ∀ w w', ‖(s w : ℂ)‖ = ‖(s w' : ℂ)‖) :
    ∃ r : ℝ, 0 < r ∧ ∀ h : HS L N, actL (scal L N s) h = r • h := by
  by_cases hne : Nonempty (InfinitePlace L)
  · obtain ⟨w0⟩ := hne
    have hs0 : (s w0 : ℂ) ≠ 0 := (s w0).ne_zero
    refine ⟨(‖(s w0 : ℂ)‖ ^ 2)⁻¹, by positivity, fun h => HS_ext fun w => ?_⟩
    have e : ((((scal L N s) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
        Matrix.scalar (Fin N) ((s w : ℂ)⁻¹) := by
      simp only [scal, ← map_inv, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val]
    rw [mat_actL, mat_smul, e]
    have hc : star ((s w : ℂ)⁻¹) * (s w : ℂ)⁻¹ = (((‖(s w0 : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', norm_inv, hs w w0]
      push_cast
      ring
    ext i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.smul_apply, Pi.star_apply]
    rw [Complex.real_smul, ← hc]
    ring
  · refine ⟨1, one_pos, fun h => HS_ext fun w => absurd ⟨w⟩ hne⟩

end PositivityTheory.KB.WhittakerCocycle

end
