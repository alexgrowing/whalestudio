import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFramesStatement

noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HolRead Filter
open scoped Topology Classical

namespace GlobalTheory.HolRead.Holo

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem differentiableAt_of_chart (Φ : V → V) (G F : V → ℂ) (M : V →L[ℝ] ℂ)
    (hΦ : HasStrictFDerivAt Φ (ContinuousLinearMap.id ℝ V) 0) (hF : HasFDerivAt F M 0)
    (hGF : ∀ᶠ w in 𝓝 (0 : V), G (Φ w) = F w) (hM : ∀ v, M (Complex.I • v) = Complex.I * M v) :
    DifferentiableAt ℂ G (Φ 0) := by
  have hΦ' : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ V : V ≃L[ℝ] V) : V →L[ℝ] V) 0 := hΦ
  set g := hΦ'.localInverse Φ _ 0 with hg
  have hg0 : g (Φ 0) = 0 := hΦ'.localInverse_apply_image
  have hgd : HasStrictFDerivAt g (((ContinuousLinearEquiv.refl ℝ V).symm : V ≃L[ℝ] V) : V →L[ℝ] V) (Φ 0) :=
    hΦ'.to_localInverse
  have hri : ∀ᶠ w in 𝓝 (Φ 0), Φ (g w) = w := hΦ'.eventually_right_inverse
  have ht : Tendsto g (𝓝 (Φ 0)) (𝓝 0) := by
    have := hgd.continuousAt.tendsto
    rwa [hg0] at this
  have heq : G =ᶠ[𝓝 (Φ 0)] fun w => F (g w) := by
    filter_upwards [hri, ht.eventually hGF] with w h1 h2
    rw [← h2, h1]
  have hF' : HasFDerivAt F M (g (Φ 0)) := by rw [hg0]; exact hF
  have h1 : HasFDerivAt G M (Φ 0) := by
    have := (hF'.comp (Φ 0) hgd.hasFDerivAt).congr_of_eventuallyEq heq
    simpa using this
  let M' : V →L[ℂ] ℂ :=
    { toFun := M
      map_add' := M.map_add
      map_smul' := fun c v => by
        have h : c • v = c.re • v + c.im • (Complex.I • v) := by
          conv_lhs => rw [← Complex.re_add_im c]
          rw [add_smul, mul_smul]; simp
        rw [h, map_add, map_smul, map_smul, hM]
        simp only [Complex.real_smul, RingHom.id_apply, smul_eq_mul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring
      cont := M.cont }
  exact (hasFDerivAt_of_restrictScalars ℝ (f' := M') h1 rfl).differentiableAt

end General

variable {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}

def oneFr (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

theorem rmul_apply (x y : Frame Ψ r) (τ : Ψ) (a c : Fin r) : rmul x y τ a c = ∑ k, x τ a k * y τ k c := rfl

theorem rmul_assoc (x y z : Frame Ψ r) : rmul (rmul x y) z = rmul x (rmul y z) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat y τ) (mat z τ)

theorem rmul_one (x : Frame Ψ r) : rmul x (oneFr Ψ r) = x := by
  funext τ
  exact Matrix.mul_one (mat x τ)

theorem one_rmul (x : Frame Ψ r) : rmul (oneFr Ψ r) x = x := by
  funext τ
  exact Matrix.one_mul (mat x τ)

theorem expFr_zero : expFr (0 : Frame Ψ r) = oneFr Ψ r := by
  funext τ
  exact (NormedSpace.exp_zero : NormedSpace.exp (0 : Matrix (Fin r) (Fin r) ℂ) = 1)

def mulL (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r →L[ℝ] Frame Ψ r →L[ℝ] Frame Ψ r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Frame Ψ r →ₗ[ℝ] Frame Ψ r) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ rmul
        (fun x x' y => by funext τ a c; simp [rmul_apply, add_mul, Finset.sum_add_distrib])
        (fun t x y => by funext τ a c; simp [rmul_apply, Finset.mul_sum, mul_assoc])
        (fun x y y' => by funext τ a c; simp [rmul_apply, mul_add, Finset.sum_add_distrib])
        (fun t x y => by funext τ a c; simp [rmul_apply, Finset.mul_sum, mul_left_comm]))

theorem mulL_apply (x y : Frame Ψ r) : mulL Ψ r x y = rmul x y := rfl

open scoped Matrix.Norms.Operator in
theorem hasStrict_exp_entry (a c : Fin r) :
    HasStrictFDerivAt (fun Z : Fin r → Fin r → ℂ => (NormedSpace.exp (Matrix.of Z) : Matrix (Fin r) (Fin r) ℂ) a c)
      ((ContinuousLinearMap.proj c : (Fin r → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj a : (Fin r → Fin r → ℂ) →L[ℝ] (Fin r → ℂ))) 0 := by
  let i : (Fin r → Fin r → ℂ) →L[ℝ] Matrix (Fin r) (Fin r) ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
  let p : Matrix (Fin r) (Fin r) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a c)
  have h0 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin r) (Fin r) ℂ → _) (1 : _ →L[ℝ] _) (i 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  have h := p.hasStrictFDerivAt.comp 0 (h0.comp 0 i.hasStrictFDerivAt)
  exact h

theorem hasStrict_expFr : HasStrictFDerivAt (expFr : Frame Ψ r → Frame Ψ r) (ContinuousLinearMap.id ℝ _) 0 := by
  refine hasStrictFDerivAt_pi'.2 fun τ => hasStrictFDerivAt_pi'.2 fun a => hasStrictFDerivAt_pi'.2 fun c => ?_
  have h := (hasStrict_exp_entry a c).comp (0 : Frame Ψ r)
    (ContinuousLinearMap.proj τ : Frame Ψ r →L[ℝ] (Fin r → Fin r → ℂ)).hasStrictFDerivAt
  exact h

def projU (Ψ : Finset (E →+* ℂ)) (r p : ℕ) : Frame Ψ r →L[ℝ] Frame Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W τ a b => if b < a then W τ a b else
        if a < b then -((sgn p a : ℝ) : ℂ) * ((sgn p b : ℝ) : ℂ) * (starRingEnd ℂ) (W τ b a) else 0
      map_add' := fun W W' => by
        funext τ a b
        simp only [Pi.add_apply, map_add]
        split_ifs <;> ring
      map_smul' := fun t W => by
        funext τ a b
        simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, RingHom.id_apply]
        split_ifs <;> ring }

theorem projU_apply (p : ℕ) (W : Frame Ψ r) (τ : Ψ) (a b : Fin r) : projU Ψ r p W τ a b =
    if b < a then W τ a b else
      if a < b then -((sgn p a : ℝ) : ℂ) * ((sgn p b : ℝ) : ℂ) * (starRingEnd ℂ) (W τ b a) else 0 := rfl

theorem sgn_mul_self (p a : ℕ) : ((sgn p a : ℝ) : ℂ) * ((sgn p a : ℝ) : ℂ) = 1 := by
  unfold sgn; split_ifs <;> simp

theorem projU_mem [NumberField E] [IsCMField E] (X : Data E r) (W : Frame X.Ψ r) :
    projU X.Ψ r X.p0 W ∈ unitLie X := by
  intro τ
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, mat,
    Matrix.of_apply, projU_apply, Matrix.zero_apply]
  have ha := sgn_mul_self X.p0 a
  have hb := sgn_mul_self X.p0 b
  rcases lt_trichotomy a b with h | h | h
  · simp only [h, h.not_gt, if_true, if_false, RCLike.star_def]
    linear_combination (-(sgn X.p0 b : ℂ) * (starRingEnd ℂ) (W τ b a)) * ha
  · subst h; simp
  · simp only [h, h.not_gt, if_true, if_false, RCLike.star_def, map_mul, map_neg, Complex.conj_ofReal,
      Complex.conj_conj]
    linear_combination (-(sgn X.p0 a : ℂ) * W τ a b) * hb

theorem smul_mem_unitLie [NumberField E] [IsCMField E] (X : Data E r) (t : ℝ) {Z : Frame X.Ψ r} (hZ : Z ∈ unitLie X) :
    t • Z ∈ unitLie X := by
  intro τ
  have h := congrArg (fun M => t • M) (hZ τ)
  have : mat (t • Z) τ = t • mat Z τ := rfl
  rw [this, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul]
  simpa using h

theorem frame_eq_sum (W : Frame Ψ r) : W = ∑ τ, ∑ a, ∑ b, W τ a b • unitFr τ a b := by
  funext τ' a' b'
  simp [Finset.sum_apply, unitFr, ite_and]

theorem ell_projU_I [NumberField E] [IsCMField E] (X : Data E r) (ℓ : Frame X.Ψ r →L[ℝ] ℂ)
    (h : ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X,
      Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) (W : Frame X.Ψ r) :
    ℓ (projU X.Ψ r X.p0 (Complex.I • W)) = Complex.I * ℓ (projU X.Ψ r X.p0 W) := by
  set P := projU X.Ψ r X.p0 with hP
  have key : ∀ (τ : X.Ψ) (a b : Fin r), ℓ (P (Complex.I • unitFr τ a b)) = Complex.I * ℓ (P (unitFr τ a b)) := by
    intro τ a b
    by_cases hab : b < a
    · have ha := sgn_mul_self X.p0 a
      have hb := sgn_mul_self X.p0 b
      set t : ℝ := -(sgn X.p0 a * sgn X.p0 b) / 2 with ht
      have h1 := h τ b a hab _ (smul_mem_unitLie X t (projU_mem X (unitFr τ a b))) _
        (smul_mem_unitLie X t (projU_mem X (Complex.I • unitFr τ a b))) (by
          funext τ' c d
          simp only [Pi.add_apply, Pi.smul_apply, projU_apply, unitFr, smul_eq_mul, Complex.real_smul, map_mul,
            Complex.conj_I]
          rcases lt_trichotomy c d with hcd | hcd | hcd
          · simp only [hcd, hcd.not_gt, if_true, if_false]
            by_cases hc : τ' = τ ∧ c = b ∧ d = a
            · obtain ⟨rfl, rfl, rfl⟩ := hc
              simp only [and_self, if_true, map_one, ht]
              push_cast
              linear_combination (-((sgn X.p0 c : ℂ) ^ 2 * (sgn X.p0 d : ℂ) ^ 2) / 2) * Complex.I_mul_I +
                ((sgn X.p0 c : ℂ) * (sgn X.p0 c : ℂ)) * ha + hb
            · have hc' : ¬ (τ' = τ ∧ d = a ∧ c = b) := fun h' => hc ⟨h'.1, h'.2.2, h'.2.1⟩
              simp [hc, hc']
          · subst hcd
            have hc : ¬ (τ' = τ ∧ c = b ∧ c = a) := fun h' => hab.ne (h'.2.1.symm.trans h'.2.2)
            simp [hc]
          · have hc : ¬ (τ' = τ ∧ c = b ∧ d = a) := fun h' => by
              obtain ⟨-, rfl, rfl⟩ := h'
              exact hab.not_gt hcd
            simp only [hcd, if_true, hc, if_false]
            linear_combination ((t : ℂ) * if τ' = τ ∧ c = a ∧ d = b then 1 else 0) * Complex.I_mul_I)
      rw [map_smul, map_smul, Complex.real_smul, Complex.real_smul] at h1
      have htt : (t : ℂ) * (-2 * ((sgn X.p0 a : ℂ) * (sgn X.p0 b : ℂ))) = 1 := by
        rw [ht]; push_cast
        linear_combination ((sgn X.p0 b : ℂ) * (sgn X.p0 b : ℂ)) * ha + hb
      have ht0 : (t : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one htt
      refine mul_left_cancel₀ ht0 ?_
      linear_combination (-Complex.I) * h1 + ((t : ℂ) * ℓ (P (Complex.I • unitFr τ a b))) * Complex.I_mul_I
    · have h0 : ∀ z : ℂ, P (z • unitFr τ a b) = 0 := by
        intro z
        funext τ' c d
        simp only [hP, projU_apply, unitFr, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rcases lt_trichotomy c d with hcd | hcd | hcd
        · have hc : ¬ (τ' = τ ∧ d = a ∧ c = b) := fun h' => by
            obtain ⟨-, rfl, rfl⟩ := h'
            exact hab hcd
          simp [hcd.not_gt, hc]
        · simp [hcd]
        · have hc : ¬ (τ' = τ ∧ c = a ∧ d = b) := fun h' => by
            obtain ⟨-, rfl, rfl⟩ := h'
            exact hab hcd
          simp [hcd, hc]
      have h1 := h0 1
      rw [one_smul] at h1
      rw [h0, h1]; simp
  have key2 : ∀ (z : ℂ) (τ : X.Ψ) (a b : Fin r),
      ℓ (P (z • unitFr τ a b)) = z * ℓ (P (unitFr τ a b)) := by
    intro z τ a b
    have h : z • unitFr τ a b = z.re • unitFr τ a b + z.im • (Complex.I • unitFr τ a b) := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [add_smul, mul_smul]; simp
    rw [h]
    simp only [map_add, map_smul, key, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im z]
    ring
  conv_lhs => rw [frame_eq_sum W]
  conv_rhs => rw [frame_eq_sum W]
  simp only [Finset.smul_sum, smul_smul, map_sum, key2, Finset.mul_sum, mul_assoc]

theorem differentiableAt_bchar (la : Wt Ψ r) :
    DifferentiableAt ℂ (fun W : Frame Ψ r => bchar la (oneFr Ψ r + W)) 0 := by
  unfold bchar
  have hp : ∀ {ι : Type} (u : Finset ι) (f : ι → Frame Ψ r → ℂ), (∀ i ∈ u, DifferentiableAt ℂ (f i) 0) →
      DifferentiableAt ℂ (fun W => ∏ i ∈ u, f i W) 0 := fun u f hf =>
    (HasFDerivAt.finset_prod fun i hi => (hf i hi).hasFDerivAt).differentiableAt
  refine hp _ _ fun τ _ => hp _ _ fun i _ => ?_
  refine DifferentiableAt.zpow ?_ (Or.inl ?_)
  · simp only [Pi.add_apply]
    fun_prop
  · show (1 : Matrix (Fin r) (Fin r) ℂ) i i + 0 ≠ 0
    simp

theorem differentiableAt_unit [NumberField E] [IsCMField E] (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (hQ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) (y : Frame X.Ψ r)
    (hy : ∀ Z ∈ unitLie X, rmul y (expFr Z) ∈ X.dom) (ℓ : Frame X.Ψ r →L[ℝ] ℂ)
    (hℓ : HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) 0)
    (h : ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X,
      Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) :
    DifferentiableAt ℂ (fun w => Q (rmul y w)) (oneFr X.Ψ r) := by
  set P := projU X.Ψ r X.p0 with hP
  have hP0 : P 0 = 0 := map_zero P
  let Φ : Frame X.Ψ r → Frame X.Ψ r := fun W => rmul (expFr (P W)) (oneFr X.Ψ r + (W - P W))
  have hΦ0 : Φ 0 = oneFr X.Ψ r := by
    simp only [Φ, hP0, expFr_zero, one_rmul, sub_zero, add_zero]
  have hΦ : HasStrictFDerivAt Φ (ContinuousLinearMap.id ℝ _) 0 := by
    have h1 : HasStrictFDerivAt (fun W => expFr (P W)) ((ContinuousLinearMap.id ℝ _).comp P) 0 :=
      HasStrictFDerivAt.comp (g := expFr) 0 (by rw [hP0]; exact hasStrict_expFr) P.hasStrictFDerivAt
    have h2 : HasStrictFDerivAt (fun W => oneFr X.Ψ r + (W - P W)) (ContinuousLinearMap.id ℝ _ - P) 0 :=
      ((hasStrictFDerivAt_id (0 : Frame X.Ψ r)).sub P.hasStrictFDerivAt).const_add _
    have h3 := (mulL X.Ψ r).hasStrictFDerivAt_of_bilinear h1 h2
    refine h3.congr_fderiv ?_
    ext1 W
    simp [mulL_apply, hP0, expFr_zero, one_rmul, rmul_one]
  obtain ⟨χ', hχ⟩ := differentiableAt_bchar (Ψ := X.Ψ) (r := r) la
  have hq : HasFDerivAt (fun W => Q (rmul y (expFr (P W)))) (ℓ.comp P) 0 := by
    have h1 : HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) (P 0) := by
      rw [hP0]; exact hℓ
    exact h1.comp_hasFDerivAt 0 P.hasFDerivAt (Eventually.of_forall fun W => projU_mem X W)
  have hF := (hχ.restrictScalars ℝ).mul hq
  have hdet : ∀ᶠ W in 𝓝 (0 : Frame X.Ψ r), ∀ τ, (mat (oneFr X.Ψ r + (W - P W)) τ).det ≠ 0 := by
    refine eventually_all.2 fun τ => ?_
    have hc : Continuous fun W : Frame X.Ψ r => (mat (oneFr X.Ψ r + (W - P W)) τ).det :=
      Continuous.matrix_det (A := fun W : Frame X.Ψ r => mat (oneFr X.Ψ r + (W - P W)) τ)
        ((continuous_apply τ).comp (continuous_const.add (continuous_id.sub P.continuous)))
    refine hc.continuousAt.eventually_ne ?_
    rw [hP0, sub_zero, add_zero]
    exact (Matrix.det_one.trans_ne one_ne_zero : (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0)
  rw [← hΦ0]
  refine differentiableAt_of_chart Φ _ _ _ hΦ hF ?_ ?_
  · filter_upwards [hdet] with W hW
    have hb : oneFr X.Ψ r + (W - P W) ∈ Bor X.Ψ r := fun τ => ⟨hW τ, fun a c hca => by
      show (1 : Matrix (Fin r) (Fin r) ℂ) a c + (W τ a c - projU X.Ψ r X.p0 W τ a c) = 0
      simp [projU_apply, hca, Matrix.one_apply_ne hca.ne']⟩
    have hχ2 : bchar la (oneFr X.Ψ r + (W - P W)) = bchar la (oneFr X.Ψ r + W) := by
      simp [bchar, hP, projU_apply]
    simp only [Φ, Pi.mul_apply]
    rw [← rmul_assoc, hQ _ (hy _ (projU_mem X W)) _ hb, hχ2]
  · intro v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, hP, ell_projU_I X ℓ h]
    ring

def invFr (x : Frame Ψ r) : Frame Ψ r := fun τ => ((mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem rmul_invFr {x : Frame Ψ r} (hx : ∀ τ, (mat x τ).det ≠ 0) : rmul x (invFr x) = oneFr Ψ r := by
  funext τ
  exact Matrix.mul_nonsing_inv (mat x τ) (hx τ).isUnit

theorem invFr_rmul {x : Frame Ψ r} (hx : ∀ τ, (mat x τ).det ≠ 0) : rmul (invFr x) x = oneFr Ψ r := by
  funext τ
  exact Matrix.nonsing_inv_mul (mat x τ) (hx τ).isUnit

theorem invFr_mem_Bor {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : invFr b ∈ Bor Ψ r := by
  intro τ
  have hu : IsUnit (mat b τ).det := (hb τ).1.isUnit
  refine ⟨(Matrix.isUnit_nonsing_inv_det (mat b τ) hu).ne_zero, fun a c hca => ?_⟩
  letI := Matrix.invertibleOfIsUnitDet _ hu
  have hT : (mat b τ).BlockTriangular id := fun i j hij => (hb τ).2 i j hij
  exact Matrix.blockTriangular_inv_of_blockTriangular hT hca

theorem differentiableOn_of_killed (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (hQ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x)
    (hk : ∀ y, IsUnitFr X y → ∃ ℓ : Frame X.Ψ r →L[ℝ] ℂ,
      HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) 0 ∧
      ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X,
        Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) :
    DifferentiableOn ℂ Q X.dom := by
  obtain ⟨g1, g2, -, g4, -, g6, -⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames E r X
  intro x hx
  obtain ⟨y, hy, b, hb, rfl⟩ := g2 x hx
  obtain ⟨ℓ, hℓ, h⟩ := hk y hy
  have hyd : ∀ τ, (mat y τ).det ≠ 0 := fun τ => (g1 y hy τ).1
  have hbd : ∀ τ, (mat b τ).det ≠ 0 := fun τ => (hb τ).1
  have hG := differentiableAt_unit X la Q hQ y (fun Z hZ => g1 _ (g6 y hy Z hZ)) ℓ hℓ h
  let A : Frame X.Ψ r → Frame X.Ψ r := fun x => rmul (invFr y) (rmul x (invFr b))
  have hA : Differentiable ℂ A := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_
    simp only [A, rmul_apply]
    fun_prop
  have hA0 : A (rmul y b) = oneFr X.Ψ r := by
    simp only [A]
    rw [rmul_assoc, rmul_invFr hbd, rmul_one, invFr_rmul hyd]
  have hcomp : DifferentiableAt ℂ (fun x => bchar la b * Q (rmul y (A x))) (rmul y b) :=
    (DifferentiableAt.comp (g := fun w => Q (rmul y w)) _ (by rw [hA0]; exact hG) (hA _)).const_mul _
  have key : ∀ x ∈ X.dom, Q x = bchar la b * Q (rmul y (A x)) := by
    intro x hx
    simp only [A]
    rw [← rmul_assoc, rmul_invFr hyd, one_rmul, ← hQ _ (g4 x hx _ (invFr_mem_Bor hb)) b hb, rmul_assoc,
      invFr_rmul hbd, rmul_one]
  exact hcomp.differentiableWithinAt.congr key (key _ hx)

end GlobalTheory.HolRead.Holo
