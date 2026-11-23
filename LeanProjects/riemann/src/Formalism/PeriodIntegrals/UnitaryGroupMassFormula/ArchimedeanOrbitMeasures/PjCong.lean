import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MpOfIsomProd

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def liftL {Z E X : Type} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup E] [Module ℝ E] [AddCommGroup X]
    [Module ℝ X] (L : E →ₗ[ℝ] X) (hL : Function.Injective L) (Ξ : Z →ₗ[ℝ] X) (h : ∀ z, ∃ x, L x = Ξ z) :
    Z →ₗ[ℝ] E :=
  (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ
    Ξ.codRestrict (LinearMap.range L) (fun z => by obtain ⟨x, hx⟩ := h z; exact ⟨x, hx⟩)

theorem liftL_spec {Z E X : Type} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup E] [Module ℝ E] [AddCommGroup X]
    [Module ℝ X] (L : E →ₗ[ℝ] X) (hL : Function.Injective L) (Ξ : Z →ₗ[ℝ] X) (h : ∀ z, ∃ x, L x = Ξ z) (z : Z) :
    L (liftL L hL Ξ h z) = Ξ z := by
  have key := (LinearEquiv.ofInjective L hL).apply_symm_apply
    (Ξ.codRestrict (LinearMap.range L) (fun z => by obtain ⟨x, hx⟩ := h z; exact ⟨x, hx⟩) z)
  exact congrArg Subtype.val key

theorem inj_of_frob {ι p q : Type} [Fintype ι] [Fintype p] [Fintype q]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix p q ℂ) (hn : ∀ t, ∑ i, ∑ j, ‖L t i j‖ ^ 2 = ‖t‖ ^ 2) :
    Function.Injective L := by
  refine (injective_iff_map_eq_zero L).mpr ?_
  intro t ht
  have h := hn t
  rw [ht] at h
  simp only [Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at h
  have h2 : ‖t‖ ^ 2 = 0 := h.symm
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

def congL {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun M := Bᴴ * M * B
  map_add' _ _ := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp

theorem congL_herm {m : ℕ} (B M : Matrix (Fin m) (Fin m) ℂ) (hM : Mᴴ = M) : (congL B M)ᴴ = congL B M := by
  show (Bᴴ * M * B)ᴴ = Bᴴ * M * B
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hM,
    Matrix.mul_assoc]

def congH {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (B : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ η :=
  liftL H (inj_of_frob H hn) (congL B ∘ₗ H) (fun s => hs _ (congL_herm B _ (hH s)))

theorem congH_spec {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (B : Matrix (Fin m) (Fin m) ℂ) (s) :
    H (congH H hH hn hs B s) = Bᴴ * H s * B := by
  unfold congH
  exact liftL_spec _ _ _ _ s

theorem cong_factor {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (B : Matrix (Fin m) (Fin m) ℂ)
    (hB : B.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ η)).map (congH H hH hn hs B) =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
  set C := congH H hH hn hs B with hCdef
  have hspec : ∀ s, H (C s) = Bᴴ * H s * B := congH_spec H hH hn hs B
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have hBh : IsUnit Bᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.2 (star_ne_zero.2 hB)
  have canc : ∀ X : Matrix (Fin m) (Fin m) ℂ, (Bᴴ)⁻¹ * (Bᴴ * X * B) * B⁻¹ = X := by
    intro X
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hBh, Matrix.one_mul]
  have hinjC : Function.Injective C := by
    intro a b hab
    apply inj_of_frob H hn
    have h1 := congrArg H hab
    rw [hspec, hspec] at h1
    rw [← canc (H a), h1, canc]
  have hdet : LinearMap.det C ≠ 0 := fun h =>
    (LinearMap.det_eq_zero_iff_ker_ne_bot.1 h) (LinearMap.ker_eq_bot.2 hinjC)
  have hC := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ η))) hdet
  set c := ENNReal.ofReal |(LinearMap.det C)⁻¹| with hc

  set mR : EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
    (reimE (r := m) (m := m)).toLinearMap ∘ₗ ((mulRC (r := m) B).restrictScalars ℝ) ∘ₗ
      (reimE (r := m) (m := m)).symm.toLinearMap with hmR
  set mL : EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
    (reimE (r := m) (m := m)).toLinearMap ∘ₗ ((mulLC (c := m) Bᴴ).restrictScalars ℝ) ∘ₗ
      (reimE (r := m) (m := m)).symm.toLinearMap with hmL
  have hmRf : (mR : _ → _) = fun y => reim (Matrix.of ((reimE (r := m) (m := m)).symm y) * B) := by
    funext y
    simp only [hmR, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulRC_apply]
    rfl
  have hmLf : (mL : _ → _) = fun y => reim (Bᴴ * Matrix.of ((reimE (r := m) (m := m)).symm y)) := by
    funext y
    simp only [hmL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulLC_apply]
    rfl
  have hR : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))).map mR =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
    rw [hmRf]; exact map_mulR B hB
  have hL : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))).map mL =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
    rw [hmLf, map_mulL Bᴴ (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hB), Matrix.det_conjTranspose,
      Complex.star_def, Complex.normSq_conj]
  have key : ∀ z : EuclideanSpace ℝ η × EuclideanSpace ℝ η, psiLp H (Prod.map C C z) = mL (mR (psiLp H z)) := by
    intro z
    rw [hmLf, hmRf]
    simp only [psiLp_apply, Prod.map_fst, Prod.map_snd, hspec]
    have e1 : ∀ M : Matrix (Fin m) (Fin m) ℂ, (reimE (r := m) (m := m)).symm (reim M) = M :=
      fun M => (reimE (r := m) (m := m)).symm_apply_apply M
    rw [e1, e1]
    congr 1
    show _ = Bᴴ * ((Complex.I • H z.1 + H z.2) * B)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hmC : Measurable C := C.continuous_of_finiteDimensional.measurable
  have hmP := psi_mp H hH hn hs
  have hmRm : Measurable mR := mR.continuous_of_finiteDimensional.measurable
  have hmLm : Measurable mL := mL.continuous_of_finiteDimensional.measurable
  have lhs : (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map (psiLp H ∘ Prod.map C C) =
      (c * c) • volume := by
    rw [← Measure.map_map hmP.measurable (hmC.prodMap hmC), Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ hmC hmC, hC, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_smul, ← Measure.volume_eq_prod, hmP.map_eq]
  have rhs : (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map (psiLp H ∘ Prod.map C C) =
      (ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ * ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹) • volume := by
    have : (psiLp H ∘ Prod.map C C) = mL ∘ mR ∘ psiLp H := funext key
    rw [this, ← Measure.map_map hmLm (hmRm.comp hmP.measurable), ← Measure.map_map hmRm hmP.measurable,
      hmP.map_eq, hR, Measure.map_smul, hL, smul_smul]
  have hball := lhs.symm.trans rhs
  have hv := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool)) => μ (Metric.ball 0 1)) hball
  simp only [Measure.smul_apply, smul_eq_mul] at hv
  have hpos : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hcc := (ENNReal.mul_left_inj hpos hfin).1 hv
  have q0 : 0 ≤ (Complex.normSq B.det ^ m)⁻¹ := inv_nonneg.2 (pow_nonneg (Complex.normSq_nonneg _) _)
  rw [hc, ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul q0,
    ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg q0 q0),
    mul_self_inj (abs_nonneg _) q0] at hcc
  rw [hC, hc, hcc]
