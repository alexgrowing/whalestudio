import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

noncomputable section

open MeasureTheory Matrix Topology
open scoped ContDiff

namespace GlobalTheory.UHContSmooth

variable {n : ℕ}

def grp (H : Matrix (Fin n) (Fin n) ℂ) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | (g : Matrix (Fin n) (Fin n) ℂ) ∈ PI.UpqRep.UH H}
  mul_mem' := by
    intro g h hg hh
    have hg' : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * g = H := hg
    have hh' : (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * h = H := hh
    show (g.1 * h.1)ᴴ * H * (g.1 * h.1) = H
    rw [conjTranspose_mul]
    calc (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H *
          ((g : Matrix (Fin n) (Fin n) ℂ) * h)
        = (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [hg', hh']
  one_mem' := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H
    simp
  inv_mem' := by
    intro g hg
    have hg' : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * g = H := hg
    show ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * H *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = H
    have h1 : ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
        (g : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv g
    calc ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * H *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        = ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
          ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * g) *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg']
      _ = H := by
          rw [show ∀ A B C D E : Matrix (Fin n) (Fin n) ℂ, A * (B * C * D) * E = (A * B) * C * (D * E)
            from fun A B C D E => by simp only [Matrix.mul_assoc], h1, h2, Matrix.one_mul, Matrix.mul_one]

def mat {H : Matrix (Fin n) (Fin n) ℂ} (g : grp H) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem left_inv {H : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ PI.UpqRep.UH H) : (H * gᴴ * H) * g = 1 := by
  have hg' : gᴴ * H * g = H := hg
  calc (H * gᴴ * H) * g = H * (gᴴ * H * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hH]

theorem range_mat {H : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) :
    Set.range (mat (H := H)) = PI.UpqRep.UH H := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hg
    have h2 := left_inv hH hg
    exact ⟨⟨⟨g, H * gᴴ * H, mul_eq_one_comm.mp h2, h2⟩, hg⟩, rfl⟩

theorem isClosedEmbedding_mat {H : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) :
    IsClosedEmbedding (mat (H := H)) := by
  have hc : Continuous (mat (H := H)) := Units.continuous_val.comp continuous_subtype_val
  let f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun g => (g, MulOpposite.op (H * gᴴ * H))
  have hf : Continuous f :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : f ∘ mat (H := H)
      = Units.embedProduct _ ∘ (Subtype.val : grp H → (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
    funext g
    simp only [Function.comp_apply, f, Units.embedProduct_apply]
    rw [Units.inv_eq_of_mul_eq_one_left (left_inv hH (g := mat g) g.2)]
    rfl
  have hi : IsInducing (mat (H := H)) := by
    refine IsInducing.of_comp hc hf ?_
    rw [hcomp]
    exact Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal
  refine ⟨⟨hi, fun a b h => Subtype.ext (Units.ext h)⟩, ?_⟩
  rw [range_mat hH]
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_contDiff {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix (Fin n) (Fin n) ℂ}
    {ρ : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ} (hH : H * H = 1) (h1 : ρ 1 = 1)
    (hmul : ∀ g ∈ PI.UpqRep.UH H, ∀ h ∈ PI.UpqRep.UH H, ρ (g * h) = ρ g * ρ h)
    (hcont : ContinuousOn ρ (PI.UpqRep.UH H)) (x₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ F : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ, ContDiff ℝ ∞ F ∧
      ∀ x ∈ Metric.ball x₀ 1, x ∈ PI.UpqRep.UH H → ρ x = F x := by
  have hemb := isClosedEmbedding_mat hH
  have hrange := range_mat hH
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  have : LocallyCompactSpace (grp H) := hemb.locallyCompactSpace
  have : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  have : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℂ _
  borelize ↥(grp H)
  set μ : Measure (grp H) := Measure.haar
  have hmem : ∀ g : grp H, mat g ∈ PI.UpqRep.UH H := fun g => g.2
  have hu : Continuous (mat (H := H)) := hemb.continuous
  have hb : Continuous fun g : grp H => ρ (mat g) := hcont.comp_continuous hu hmem
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ PI.UpqRep.UH H := hmem 1
  have hnb : {g | ‖ρ g - 1‖ < 1 / 2} ∈ 𝓝[PI.UpqRep.UH H] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hcont 1 hone) (Metric.ball_mem_nhds _ (half_pos one_pos))
    simpa [h1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφU, hφc, hφ, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  have hψ : Continuous fun g : grp H => φ (mat g) := hφ.continuous.comp hu
  have hψc : HasCompactSupport fun g : grp H => φ (mat g) := hφc.comp_isClosedEmbedding hemb
  have hcs : HasCompactSupport fun g : grp H => φ (mat g) • ρ (mat g) := hψc.smul_right
  have hcn : Continuous fun g : grp H => φ (mat g) • ρ (mat g) := hψ.smul hb
  have hint := Continuous.integrable_of_hasCompactSupport (E := Matrix ι ι ℂ) (μ := μ) hcn hcs
  have hψi : Integrable (fun g : grp H => φ (mat g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : grp H, φ (mat g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  set c := ∫ g : grp H, φ (mat g) ∂μ with hc
  set M := ∫ g : grp H, φ (mat g) • ρ (mat g) ∂μ with hM
  have hMu : IsUnit M := by
    have e1 : ∫ g : grp H, (φ (mat g) • ρ (mat g) - φ (mat g) • (1 : Matrix ι ι ℂ)) ∂μ
        = M - c • (1 : Matrix ι ι ℂ) := by
      rw [integral_sub hint (hψi.smul_const _), integral_smul_const]
    have e2 : ‖∫ g : grp H, (φ (mat g) • ρ (mat g) - φ (mat g) • (1 : Matrix ι ι ℂ)) ∂μ‖
        ≤ ∫ g : grp H, φ (mat g) * (1 / 2) ∂μ := by
      refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
      by_cases hg : φ (mat g) = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hUs ⟨hφU (subset_tsupport _ hg), hmem g⟩)) (hφ0 _)
    rw [e1, integral_mul_const, ← hc] at e2
    have e3 : ‖-(c⁻¹ • (M - c • (1 : Matrix ι ι ℂ)))‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_of_nonneg (inv_pos.2 hpos).le, inv_mul_lt_iff₀ hpos]
      linarith
    have e4 := isUnit_one_sub_of_norm_lt_one e3
    have e5 : M = (c • (1 : Matrix ι ι ℂ)) * (1 - -(c⁻¹ • (M - c • (1 : Matrix ι ι ℂ)))) := by
      rw [Matrix.smul_mul, Matrix.one_mul, sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hpos.ne',
        one_smul]
      abel
    rw [e5]
    refine IsUnit.mul (IsUnit.of_mul_eq_one (c⁻¹ • (1 : Matrix ι ι ℂ)) ?_) e4
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  obtain ⟨N, hN⟩ := hMu.exists_right_inv
  let y : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun x => H * xᴴ * H
  have hy : ContDiff ℝ ∞ y := (contDiff_const.mul GlobalTheory.GardingVec.contDiff_conjTranspose).mul contDiff_const
  have hform : ∀ x ∈ PI.UpqRep.UH H, ρ x * M = ∫ g : grp H, φ (y x * mat g) • ρ (mat g) ∂μ := by
    intro x hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (mat (H := H)) := by rw [hrange]; exact hx
    have e0 := ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ) (ρ x)) hint
    simp only [ContinuousLinearMap.mul_apply'] at e0
    rw [hM, ← e0,
      ← integral_mul_left_eq_self (fun g : grp H => φ (y x * mat g) • ρ (mat g)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : mat (z * g) = x * mat g := by rw [← hz]; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, show y x * x = 1 from left_inv hH hx, Matrix.one_mul, hmul _ hx _ (hmem g),
      Matrix.mul_smul]
  have hC : IsCompact (Set.image2 (· * ·) (Metric.closedBall x₀ 1) (tsupport φ)) :=
    (isCompact_closedBall x₀ 1).mul hφc
  have hK := hemb.isCompact_preimage hC
  have hs : ContDiff ℝ ∞ fun x => ∫ g in (mat (H := H)) ⁻¹'
      (Set.image2 (· * ·) (Metric.closedBall x₀ 1) (tsupport φ)), φ (y x * mat g) • ρ (mat g) ∂μ :=
    contDiff_infty.2 fun m => GlobalTheory.GardingVec.contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
      (fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × Matrix ι ι ℂ) =>
        φ (y z.1 * z.2.1) • z.2.2)
      ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
        (contDiff_snd.comp contDiff_snd))
  refine ⟨_, hs.mul (contDiff_const (c := N)), fun x hx hxG => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_, ← hform x hxG, Matrix.mul_assoc, hN,
    Matrix.mul_one]
  by_contra hne
  refine hg ⟨x, Metric.ball_subset_closedBall hx, y x * mat g,
    subset_tsupport _ fun h => hne (by rw [h, zero_smul]), ?_⟩
  show x * (y x * mat g) = mat g
  rw [← Matrix.mul_assoc, show x * y x = 1 from mul_eq_one_comm.1 (left_inv hH hxG), Matrix.one_mul]

theorem exists_contDiff_entry {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix (Fin n) (Fin n) ℂ}
    {ρ : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ} (hH : H * H = 1) (h1 : ρ 1 = 1)
    (hmul : ∀ g ∈ PI.UpqRep.UH H, ∀ h ∈ PI.UpqRep.UH H, ρ (g * h) = ρ g * ρ h)
    (hcont : ∀ i j, ContinuousOn (fun g => ρ g i j) (PI.UpqRep.UH H)) (i j : ι)
    (x₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : (Fin n → Fin n → ℂ) → ℂ), IsOpen U ∧ x₀ ∈ U ∧
      ContDiff ℝ ∞ F ∧ ∀ x ∈ U, x ∈ PI.UpqRep.UH H → ρ x i j = F (Matrix.of.symm x) := by
  obtain ⟨F, hF, hFe⟩ := exists_contDiff hH h1 hmul
    (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hcont i j) x₀
  let A : (Fin n → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => Matrix.of p
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let B : Matrix ι ι ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun m => m i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨Metric.ball x₀ 1, fun p => B (F (A p)), Metric.isOpen_ball, Metric.mem_ball_self one_pos,
    (LinearMap.toContinuousLinearMap B).contDiff.comp
      (hF.comp (LinearMap.toContinuousLinearMap A).contDiff), fun x hx hxG => ?_⟩
  rw [hFe x hx hxG]
  rfl

end

theorem smoothOnH_of_continuousOn : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (H : Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ), H * H = 1 → ρ 1 = 1 →
    (∀ g ∈ PI.UpqRep.UH H, ∀ h ∈ PI.UpqRep.UH H, ρ (g * h) = ρ g * ρ h) →
    (∀ i j, ContinuousOn (fun g => ρ g i j) (PI.UpqRep.UH H)) →
    ∀ i j, PI.UpqRep.SmoothOnH H (fun g => ρ g i j) := by
  intro n ι _ _ H ρ hH h1 hmul hcont i j x₀ _
  obtain ⟨U, F, hU, hx, hF, hFe⟩ := exists_contDiff_entry hH h1 hmul hcont i j x₀
  exact ⟨U, F, hU, hx, hF.contDiffOn, hFe⟩

end GlobalTheory.UHContSmooth
