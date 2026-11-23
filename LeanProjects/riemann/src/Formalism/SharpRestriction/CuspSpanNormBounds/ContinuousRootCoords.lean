import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Meas2

variable {k r : ℕ} {κ τ : ℝ}

theorem ofReal_ne_zero_of_pos {α : ℝ} (hα : 0 < α) : ENNReal.ofReal α ≠ 0 := (ENNReal.ofReal_pos.mpr hα).ne'

theorem map_cjT_cjIT_smul (hκ : 0 < κ) (hτ : 0 < τ) {α : ℝ} (hα : 0 < α) (μ₁ : Measure (Mt k r)) :
    ENNReal.ofReal α • ((ENNReal.ofReal α)⁻¹ • μ₁.map (cjIT k r κ τ)).map (cjT k r κ τ) = μ₁ := by
  rw [Measure.map_smul, Measure.map_map measurable_cjT continuous_cjIT.measurable]
  have e : cjT k r κ τ ∘ cjIT k r κ τ = id := funext (cjT_cjIT hκ hτ)
  rw [e, Measure.map_id, smul_smul, ENNReal.mul_inv_cancel (ofReal_ne_zero_of_pos hα) ENNReal.ofReal_ne_top,
    one_smul]

theorem phiP_phiPI (hκ : 0 < κ) (hτ : 0 < τ) (p : PairSp k r) : phiP k r κ τ (phiPI k r κ τ p) = p :=
  Prod.ext (Prod.ext (cjT_cjIT hκ hτ _) (cjT_cjIT hκ hτ _)) (Prod.ext (cjT_cjIT hκ hτ _) (cjT_cjIT hκ hτ _))

theorem use₉ (hκ : 0 < κ) (hτ : 0 < τ) {α : ℝ} (hα : 0 < α) (ν₁ : Measure (PairSp k r)) :
    (ENNReal.ofReal α)⁻¹ • (ENNReal.ofReal α • ν₁.map (phiPI k r κ τ)).map (phiP k r κ τ) = ν₁ := by
  rw [Measure.map_smul, Measure.map_map measurable_phiP measurable_phiPI]
  have e : phiP k r κ τ ∘ phiPI k r κ τ = id := funext (phiP_phiPI hκ hτ)
  rw [e, Measure.map_id, smul_smul, ENNReal.inv_mul_cancel (ofReal_ne_zero_of_pos hα) ENNReal.ofReal_ne_top,
    one_smul]

theorem stabAct_phiP (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) (x : PairSp k r) :
    stabAct (cj k r κ τ g) (cj k r κ τ a) (phiP k r κ τ x) = phiP k r κ τ (stabAct g a x) := by
  obtain ⟨⟨h, n⟩, ⟨h', n'⟩⟩ := x
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · funext i j
    show (cj k r κ τ a * cj k r κ τ (Matrix.of n)) i j = cj k r κ τ (a * Matrix.of n) i j
    rw [cj_mul hκ hτ]
  · funext i j
    show ((cj k r κ τ g)⁻¹ * cj k r κ τ a * cj k r κ τ g * cj k r κ τ (Matrix.of n')) i j =
      cj k r κ τ (g⁻¹ * a * g * Matrix.of n') i j
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]

theorem isOrbQuot_map_iff (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r)
    (hP : pairMeas L₁ = (pairMeas L).map (phiP k r κ τ))
    (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)) {α : ℝ} (hα : 0 < α) :
    IsOrbQuot L₁ (cj k r κ τ g) (ENNReal.ofReal α • μR.map (cjT k r κ τ))
        ((ENNReal.ofReal α)⁻¹ • ν.map (phiP k r κ τ)) ↔ IsOrbQuot L g μR ν := by
  have ha0 := ofReal_ne_zero_of_pos hα
  have hat : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : ∀ f : PairSp k r → ENNReal,
      ∫⁻ x, (∫⁻ a, f (stabAct (cj k r κ τ g) (Matrix.of a) x) ∂(ENNReal.ofReal α • μR.map (cjT k r κ τ)))
        ∂((ENNReal.ofReal α)⁻¹ • ν.map (phiP k r κ τ)) =
      ∫⁻ x, (∫⁻ a, f (phiP k r κ τ (stabAct g (Matrix.of a) x)) ∂μR) ∂ν := by
    intro f
    have inner : ∀ x, ∫⁻ a, f (stabAct (cj k r κ τ g) (Matrix.of a) x)
        ∂(ENNReal.ofReal α • μR.map (cjT k r κ τ)) =
        ENNReal.ofReal α * ∫⁻ a, f (stabAct (cj k r κ τ g) (cj k r κ τ (Matrix.of a)) x) ∂μR := by
      intro x
      rw [lintegral_smul_measure, smul_eq_mul, ← cjE_coe hκ hτ, lintegral_map_equiv]
      rfl
    simp_rw [inner]
    rw [lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ hat, ← mul_assoc,
      ENNReal.inv_mul_cancel ha0 hat, one_mul, ← phiE_coe hκ hτ, lintegral_map_equiv]
    simp only [phiE_coe, stabAct_phiP hκ hτ]
  have hs : ∀ y, (phiE hκ hτ).symm (phiP k r κ τ y) = y := fun y => (phiE hκ hτ).symm_apply_apply y
  unfold IsOrbQuot
  rw [hP]
  constructor
  · intro h f hf
    have h1 := h (f ∘ (phiE hκ hτ).symm) (hf.comp (phiE hκ hτ).symm.measurable)
    rw [key (f ∘ (phiE hκ hτ).symm)] at h1
    rw [← phiE_coe hκ hτ, lintegral_map_equiv] at h1
    simp only [Function.comp_apply, phiE_coe, hs] at h1
    exact h1
  · intro h f hf
    rw [key f, ← phiE_coe hκ hτ, lintegral_map_equiv]
    exact h (fun y => f (phiE hκ hτ y)) (hf.comp (phiE hκ hτ).measurable)

theorem IsOrbQuot_trD_iff (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)) {α : ℝ} (hα : 0 < α) :
    IsOrbQuot (trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) hz hz' hπ hπ' hμW hμW') (cj k r κ τ g)
        (ENNReal.ofReal α • μR.map (cjT k r κ τ)) ((ENNReal.ofReal α)⁻¹ • ν.map (phiP k r κ τ)) ↔
      IsOrbQuot L g μR ν :=
  isOrbQuot_map_iff hκ hτ L _ (pairMeas_trD hκ hτ L hz hz' hπ hπ' hμW hμW') g μR ν hα

def scC {P : Type*} [Fintype P] (lam : P → ℝ) : (P → ℂ) →ₗ[ℝ] (P → ℂ) :=
  LinearMap.pi fun p => (lam p • LinearMap.id) ∘ₗ LinearMap.proj p

theorem scC_apply {P : Type*} [Fintype P] (lam : P → ℝ) (v : P → ℂ) (p : P) :
    scC lam v p = ((lam p : ℝ) : ℂ) * v p := by
  simp [scC, Complex.real_smul]

theorem det_scC {P : Type*} [Fintype P] (lam : P → ℝ) : LinearMap.det (scC lam) = ∏ p, lam p ^ 2 := by
  rw [scC, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one]

theorem map_scC_volume {P : Type*} [Fintype P] (lam : P → ℝ) (h : ∀ p, lam p ≠ 0) :
    (volume : Measure (P → ℂ)).map (fun v p => ((lam p : ℝ) : ℂ) * v p) =
      ENNReal.ofReal (∏ p, lam p ^ 2)⁻¹ • volume := by
  have hd : LinearMap.det (scC lam) ≠ 0 := by
    rw [det_scC]; exact Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ (h p)
  have e : (fun (v : P → ℂ) p => ((lam p : ℝ) : ℂ) * v p) = ⇑(scC lam) :=
    funext fun v => funext fun p => (scC_apply lam v p).symm
  rw [e, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd, det_scC,
    abs_of_nonneg (inv_nonneg.mpr (Finset.prod_nonneg fun p _ => sq_nonneg _))]

theorem continuous_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (γ : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z γ) := by
  refine continuous_pi fun p => ?_
  by_cases hi : (p.1.1 : ℕ) < r
  · have e : (fun x => rootCoords k r z γ x p) =
        fun x : Mt k r => ((Matrix.of x : Mx k r) *ᵥ fvec k r z p.1.2) (eI k r ⟨p.1.1.val, hi⟩) := by
      funext x; simp only [rootCoords, flagMat, dif_pos hi]
    rw [e]
    have hc : Continuous fun x : Mt k r => ((Matrix.of x : Mx k r) *ᵥ fvec k r z p.1.2) :=
      Continuous.matrix_mulVec (A := fun x : Mt k r => (Matrix.of x : Mx k r)) (B := fun _ => fvec k r z p.1.2)
        continuous_id continuous_const
    exact (continuous_apply (eI k r ⟨p.1.1.val, hi⟩)).comp hc
  · have e : (fun x => rootCoords k r z γ x p) = fun _ : Mt k r => (if p.1.1 = p.1.2 then (1 : ℂ) else 0) := by
      funext x; simp only [rootCoords, flagMat, dif_neg hi]
    rw [e]
    exact continuous_const

theorem isRootMeas_congr_pat (L : LocBessel k r) {γ₁ γ : Point ℂ (r + 1)} (h : rootPat γ₁ = rootPat γ)
    (g : Mx k r) (μR : Measure (Mt k r)) : IsRootMeas L γ₁ g μR ↔ IsRootMeas L γ g μR := by
  unfold IsRootMeas rootCoords
  rw [h]

theorem ar1 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ * (a * c) * b = c := by
  rw [mul_inv]
  calc a⁻¹ * b⁻¹ * (a * c) * b = (a⁻¹ * a) * (b⁻¹ * b) * c := by ring
    _ = c := by rw [inv_mul_cancel₀ ha, inv_mul_cancel₀ hb]; ring

theorem ar2 {a b c : ℝ} (hb : b ≠ 0) : a * b * c * b⁻¹ = a * c := by
  calc a * b * c * b⁻¹ = a * c * (b * b⁻¹) := by ring
    _ = a * c := by rw [mul_inv_cancel₀ hb, mul_one]

theorem isRootMeas_map_iff (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r) (hz₁ : L₁.z = (τ : ℂ) • L.z)
    (hc₁ : L₁.c = (κ : ℂ) * L.c) (γ : Point ℂ (r + 1)) (g : Mx k r) (μR : Measure (Mt k r)) :
    IsRootMeas L₁ γ (cj k r κ τ g) (ENNReal.ofReal (alphaPt κ τ γ) • μR.map (cjT k r κ τ)) ↔
      IsRootMeas L γ g μR := by
  have hz := L.hz.1
  obtain ⟨lam, hlam_def⟩ : ∃ lam : rootPat γ → ℝ, lam = fun p => tF r κ τ p.1.2.val / tF r κ τ p.1.1.val :=
    ⟨_, rfl⟩
  have hlam : ∀ p, 0 < lam p := fun p => by
    rw [hlam_def]; exact div_pos (tF_pos hκ hτ _) (tF_pos hκ hτ _)
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = ∏ p, lam p ^ 2 := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hB_def]; exact Finset.prod_pos fun p _ => pow_pos (hlam p) 2
  have hA : alphaPt κ τ γ = κ ^ (rootPat γ).card * B := by
    rw [hB_def, hlam_def]; unfold alphaPt; rw [← Finset.prod_coe_sort]
  have hApos : 0 < alphaPt κ τ γ := by rw [hA]; exact mul_pos (pow_pos hκ _) hB
  have hκn : κ ^ (rootPat γ).card ≠ 0 := pow_ne_zero _ hκ.ne'
  obtain ⟨D, hD⟩ : ∃ D : (rootPat γ → ℂ) → (rootPat γ → ℂ), D = fun v p => ((lam p : ℝ) : ℂ) * v p := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : (rootPat γ → ℂ) → (rootPat γ → ℂ), D' = fun v p => (((lam p)⁻¹ : ℝ) : ℂ) * v p :=
    ⟨_, rfl⟩
  have hDm : Measurable D := by
    rw [hD]; exact (continuous_pi fun p => continuous_const.mul (continuous_apply p)).measurable
  have hD'm : Measurable D' := by
    rw [hD']; exact (continuous_pi fun p => continuous_const.mul (continuous_apply p)).measurable
  have hDD : D' ∘ D = id := by
    funext v p
    rw [hD, hD']
    show (((lam p)⁻¹ : ℝ) : ℂ) * (((lam p : ℝ) : ℂ) * v p) = v p
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (hlam p).ne', Complex.ofReal_one, one_mul]
  have hRc := (continuous_rootCoords (k := k) (r := r) L.z γ).measurable
  have hcomp : rootCoords k r ((τ : ℂ) • L.z) γ ∘ cjT k r κ τ = D ∘ rootCoords k r L.z γ :=
    funext fun x => funext fun p => by rw [hD, hlam_def]; exact rootCoords_cjT hκ hτ hz γ x p
  have hmap : (ENNReal.ofReal (alphaPt κ τ γ) • μR.map (cjT k r κ τ)).map (rootCoords k r ((τ : ℂ) • L.z) γ) =
      ENNReal.ofReal (alphaPt κ τ γ) • (μR.map (rootCoords k r L.z γ)).map D := by
    rw [Measure.map_smul, Measure.map_map (continuous_rootCoords _ γ).measurable measurable_cjT, hcomp,
      ← Measure.map_map hDm hRc]
  have hnorm : (‖(κ : ℂ) * L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card =
      κ ^ (rootPat γ).card * (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le, mul_div_assoc, mul_pow]
  have hB' : ∏ p, ((lam p)⁻¹) ^ 2 = B⁻¹ := by
    rw [hB_def, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun p _ => inv_pow _ _
  have hC0 : 0 ≤ (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card := by positivity
  have hvolD : (volume : Measure (rootPat γ → ℂ)).map D = ENNReal.ofReal B⁻¹ • volume := by
    rw [hD, map_scC_volume lam (fun p => (hlam p).ne'), ← hB_def]
  have hvolD' : (volume : Measure (rootPat γ → ℂ)).map D' = ENNReal.ofReal B • volume := by
    rw [hD', map_scC_volume (fun p => (lam p)⁻¹) (fun p => inv_ne_zero (hlam p).ne'), hB', inv_inv]
  unfold IsRootMeas
  rw [hz₁, hc₁]
  apply and_congr
  · rw [Measure.smul_apply, smul_eq_mul, ← cjE_coe hκ hτ, MeasurableEquiv.map_apply, mul_eq_zero]
    have hset : (cjE hκ hτ) ⁻¹' {x : Mt k r | Matrix.of x ∉ RStab k r (cj k r κ τ g)} =
        {x : Mt k r | Matrix.of x ∉ RStab k r g} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, cjE_coe, of_cjT, cj_mem_RStab_iff hκ hτ]
    rw [hset]
    exact or_iff_right (ofReal_ne_zero_of_pos hApos)
  · rw [hmap, hnorm]
    constructor
    · intro h
      have h2 : (μR.map (rootCoords k r L.z γ)).map D = (ENNReal.ofReal (alphaPt κ τ γ))⁻¹ •
          ENNReal.ofReal (κ ^ (rootPat γ).card * (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card) • volume := by
        rw [← h, smul_smul, ENNReal.inv_mul_cancel (ofReal_ne_zero_of_pos hApos) ENNReal.ofReal_ne_top,
          one_smul]
      have hX : μR.map (rootCoords k r L.z γ) = ((μR.map (rootCoords k r L.z γ)).map D).map D' := by
        rw [Measure.map_map hD'm hDm, hDD, Measure.map_id]
      rw [hX, h2, Measure.map_smul, Measure.map_smul, hvolD', smul_smul, smul_smul]
      congr 1
      rw [← ENNReal.ofReal_inv_of_pos hApos, ← ENNReal.ofReal_mul (inv_nonneg.mpr hApos.le),
        ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hApos.le) (mul_nonneg (pow_nonneg hκ.le _) hC0)), hA]
      congr 1
      exact ar1 hκn hB.ne'
    · intro h
      rw [h, Measure.map_smul, hvolD, smul_smul, smul_smul]
      congr 1
      rw [← ENNReal.ofReal_mul hApos.le, ← ENNReal.ofReal_mul (mul_nonneg hApos.le hC0), hA]
      congr 1
      exact ar2 hB.ne'

theorem IsRootMeas_trD_iff (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {γ₁ γ : Point ℂ (r + 1)} (hγ : rootPat γ₁ = rootPat γ) (g : Mx k r) (μR : Measure (Mt k r)) :
    IsRootMeas (trD L κ τ κN₁ hz hz' hπ hπ' hμW hμW') γ₁ (cj k r κ τ g)
        (ENNReal.ofReal (alphaPt κ τ γ) • μR.map (cjT k r κ τ)) ↔ IsRootMeas L γ g μR := by
  rw [isRootMeas_congr_pat _ hγ]
  exact isRootMeas_map_iff hκ hτ L _ rfl rfl γ g μR

end Meas2

end Formalism.MainNotions.FrameBoundFromBesselTorus
