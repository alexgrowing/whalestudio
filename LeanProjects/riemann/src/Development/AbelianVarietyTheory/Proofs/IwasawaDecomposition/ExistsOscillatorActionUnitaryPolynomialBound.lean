import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOscillatorIntegralSymplecticPathStatement

noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.OscBound

open GlobalTheory.RealWeil.Osc GlobalTheory.RealWeil.UnitaryOsc

section General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} {G : Type} [Group G] {k : G →* (V →L[ℝ] V)} {c : G → ℂ}

theorem isOsc_osc (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ)
    (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) (hc : c 1 = 1) (hl : ∀ g, star (c g) * c g * lam (k g) = 1)
    (hm : ∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) :
    IsOsc ρ (fun g v => k g v) (osc h hk c) := by
  refine ⟨fun g f f' hf hf' => ?_, fun g a f _ => intw_smul a f, fun g f hf => sm_osc hJ h hk g hf,
    fun f hf => osc_one hJ h hk hc hf, fun g g' f hf => osc_mul hJ h hk hl hm g g' hf,
    fun g v f hf => osc_heis hJ h hk g v hf, fun g A hA f hf => ?_,
    fun H _ _ _ Φ hΦ g f hf => norm_osc hJ h hk hl Φ hΦ g hf⟩
  · exact intw_add (h.twist (k g) (hk g)) (vacOp_proj hJ h hk g) (good_of_sm hJ h hf) (good_of_sm hJ h hf')
  · refine intw_comm (h.twist (k g) (hk g)) (vacOp_proj hJ h hk g) (good_of_sm hJ h hf) A hA (fun v => hA _)
      fun x => ?_
    rw [vacOp_apply, vacOp_apply, map_smul, proj_comm (h.twist (k g) (hk g)) A (fun v => hA _), proj_comm h A hA]

theorem osc_eq (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) (g : G) (f : B) :
    osc h hk c g f = c g • ∫ w, ρ (k g w) (∫ u, gau u • ρ (k g u) (proj h (ρ (-w) f))) := by
  simp only [osc, intw, vacOp_apply, map_smul, integral_smul]
  rfl

theorem norm_osc_le (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ)
    (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) {f : B} (hf : Sm ρ f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g, ‖osc h hk c g f‖ ≤ ‖c g‖ * K := by
  refine ⟨∫ w, (∫ u : V, ‖gau u‖) * ‖proj h (ρ (-w) f)‖,
    integral_nonneg fun w => mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _), fun g => ?_⟩
  rw [osc_eq, norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine norm_integral_le_of_norm_le ((good_integrable (good_of_sm hJ h hf)).const_mul _)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [h.2.2.1]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, h.2.2.1]
  rw [integral_mul_const]

theorem hasDerivAt_osc (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ)
    (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) (hc : c 1 = 1) (γ : ℝ → G) (hγ : γ 0 = 1) (X : V →L[ℝ] V)
    (hX : HasDerivAt (fun t => k (γ t)) X 0) (hcγ : DifferentiableAt ℝ (fun t => c (γ t)) 0)
    {κ : Type} [Fintype κ] (a : κ → ℂ) (p q : κ → V) (hq : IsQuadOf (omJ J) X a p q) :
    ∃ lam : ℂ, ∀ f, Sm ρ f → HasDerivAt (fun t => osc h hk c (γ t) f) (quad ρ a p q f + lam • f) 0 := by
  obtain ⟨l, hl⟩ := GlobalTheory.T.hasDerivAt_oscillatorIntegral_symplecticPath V B J ρ hJ h (fun t => k (γ t)) X (by simp only [hγ, map_one]) hX
    (fun t => hk (γ t)) κ a p q hq
  refine ⟨l + deriv (fun t => c (γ t)) 0, fun f hf => ?_⟩
  have h1 := hcγ.hasDerivAt.fun_smul (hl f hf)
  have h2 := osc_one hJ h hk hc hf
  rw [osc_eq, hc, one_smul] at h2
  simp only [hγ, hc, one_smul, h2] at h1
  simp only [osc_eq]
  rw [add_smul, ← add_assoc]
  exact h1

end General

section Transport

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem dH_comp (E : V ≃L[ℝ] V') (ρ : V' → B →L[ℂ] B) (v : V) (f : B) :
    dH (fun u => ρ (E u)) v f = dH ρ (E v) f := by
  have := E.comp_right_fderiv (f := fun u => ρ u f) (x := 0)
  rw [map_zero] at this
  exact congrArg (fun T : V →L[ℝ] B => T v) this

theorem quad_comp (E : V ≃L[ℝ] V') (ρ : V' → B →L[ℂ] B) {κ : Type} [Fintype κ] (a : κ → ℂ) (p q : κ → V') (f : B) :
    quad (fun u => ρ (E u)) a (fun i => E.symm (p i)) (fun i => E.symm (q i)) f = quad ρ a p q f := by
  simp only [quad, dH_comp, E.apply_symm_apply]

theorem isQuadOf_comp (E : V ≃L[ℝ] V') {om : V' → V' → ℝ} {om' : V → V → ℝ} (hE : ∀ x y, om (E x) (E y) = om' x y)
    {X : V' → V'} {X' : V → V} (hX : ∀ v, E (X' v) = X (E v)) {κ : Type} [Fintype κ] {a : κ → ℂ} {p q : κ → V'}
    (h : IsQuadOf om X a p q) : IsQuadOf om' X' a (fun i => E.symm (p i)) (fun i => E.symm (q i)) := by
  intro l v
  have := h (l ∘ₗ (E.symm : V' →L[ℝ] V).toLinearMap) (E v)
  simp only [← hE, E.apply_symm_apply]
  rw [← hX] at this
  simpa using this

end Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem norm_det_le (T : (ι → ι → ℂ) →L[ℝ] (ι → ι → ℂ)) (C : ι → ι → ℂ) :
    ∃ K : ℝ, ∀ M : ι → ι → ℂ, ‖(Matrix.of (T M + C)).det‖ ≤ K * (1 + ∑ i, ∑ j, ‖M i j‖) ^ Fintype.card ι := by
  refine ⟨(Fintype.card ι).factorial * (‖T‖ + ‖C‖) ^ Fintype.card ι, fun M => ?_⟩
  have hS : 0 ≤ ∑ i, ∑ j, ‖M i j‖ := by positivity
  have hM : ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ := by
    refine (pi_norm_le_iff_of_nonneg hS).2 fun i => (pi_norm_le_iff_of_nonneg hS).2 fun j => ?_
    exact (Finset.single_le_sum (f := fun j => ‖M i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖) (fun _ _ => by positivity) (Finset.mem_univ i))
  have := Matrix.det_le (A := Matrix.of (T M + C)) (abv := NormedField.toAbsoluteValue ℂ)
    (x := (‖T‖ + ‖C‖) * (1 + ∑ i, ∑ j, ‖M i j‖)) fun i j => by
      change ‖(T M + C) i j‖ ≤ _
      refine ((norm_le_pi_norm ((T M + C) i) j).trans (norm_le_pi_norm (T M + C) i)).trans ?_
      refine (norm_add_le _ _).trans ?_
      have h1 := T.le_opNorm M
      have h2 := mul_le_mul_of_nonneg_left hM (norm_nonneg T)
      nlinarith [norm_nonneg T, norm_nonneg C, mul_nonneg (norm_nonneg C) hS]
  rw [nsmul_eq_mul, mul_pow, ← mul_assoc] at this
  exact this

theorem differentiableAt_det {M : ℝ → ι → ι → ℂ} (hM : DifferentiableAt ℝ M 0) :
    DifferentiableAt ℝ (fun t => (Matrix.of (M t)).det) 0 := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  exact DifferentiableAt.fun_finset_prod fun i _ => differentiableAt_pi.1 (differentiableAt_pi.1 hM _) _

def sand (A A' : Matrix ι ι ℂ) : (ι → ι → ℂ) →L[ℝ] (ι → ι → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Matrix.of.symm (A * Matrix.of M * A')
      map_add' := fun M N => by
        change A * (Matrix.of M + Matrix.of N) * A' = A * Matrix.of M * A' + A * Matrix.of N * A'
        rw [mul_add, add_mul]
      map_smul' := fun r M => by
        change A * (r • Matrix.of M) * A' = r • (A * Matrix.of M * A')
        rw [Matrix.mul_smul, Matrix.smul_mul] }

def kLL (ι : Type) [Fintype ι] : (ι → ι → ℂ) →L[ℝ] (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => kL (Matrix.of M)
      map_add' := fun M N => ContinuousLinearMap.ext fun v => (crd ι).injective (by
        rw [ContinuousLinearMap.add_apply, map_add (crd ι), crd_kL, crd_kL, crd_kL, ← add_mulVec]; rfl)
      map_smul' := fun r M => ContinuousLinearMap.ext fun v => (crd ι).injective (by
        rw [RingHom.id_apply, ContinuousLinearMap.smul_apply, map_smul (crd ι), crd_kL, crd_kL, ← smul_mulVec]; rfl) }

theorem detPlus_sandwich (s A A' M : Matrix ι ι ℂ) : dP s (A * M * A') =
    (Matrix.of (sand ((1 / 2 : ℂ) • ((1 + s) * A)) A' (Matrix.of.symm M) +
      Matrix.of.symm ((1 / 2 : ℂ) • (1 - s)))).det := by
  change _ = (((1 / 2 : ℂ) • ((1 + s) * A)) * M * A' + (1 / 2 : ℂ) • (1 - s)).det
  simp only [dP, smul_mul_assoc, mul_assoc]

theorem hasDerivAt_kL (A A' : Matrix ι ι ℂ) {M : ℝ → Matrix ι ι ℂ} {X : Matrix ι ι ℂ}
    (hX : ∀ i j, HasDerivAt (fun t => M t i j) (X i j) 0) :
    HasDerivAt (fun t => kL (A * M t * A')) (kL (A * X * A')) 0 := by
  have hX' : HasDerivAt (fun t => (Matrix.of.symm (M t) : ι → ι → ℂ)) (Matrix.of.symm X) 0 :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hX i j
  have e : ∀ N : Matrix ι ι ℂ, kL (A * N * A') = ((kLL ι).comp (sand A A')) (Matrix.of.symm N) := fun _ => rfl
  simp only [e]
  exact ((kLL ι).comp (sand A A')).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hX'

theorem differentiableAt_dP (s A A' : Matrix ι ι ℂ) {M : ℝ → Matrix ι ι ℂ} {X : Matrix ι ι ℂ}
    (hX : ∀ i j, HasDerivAt (fun t => M t i j) (X i j) 0) :
    DifferentiableAt ℝ (fun t => dP s (A * M t * A')) 0 := by
  have hX' : HasDerivAt (fun t => (Matrix.of.symm (M t) : ι → ι → ℂ)) (Matrix.of.symm X) 0 :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hX i j
  simp only [detPlus_sandwich]
  exact differentiableAt_det
    (((ContinuousLinearMap.differentiableAt _).comp (0 : ℝ) hX'.differentiableAt).add_const _)

def kM {G : Type} [Group G] (m : G →* Matrix ι ι ℂ) : G →* (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) where
  toFun g := kL (m g)
  map_one' := by rw [map_one, kL_one]
  map_mul' g g' := by rw [map_mul, kL_mul]

theorem crd_kM {G : Type} [Group G] (m : G →* Matrix ι ι ℂ) (g : G) (v : EuclideanSpace ℂ ι) :
    crd ι (kM m g v) = m g *ᵥ crd ι v := crd_kL _ v

theorem omJ_kM {s : Matrix ι ι ℂ} (hs1 : sᴴ = s) (hs2 : s * s = 1) {G : Type} [Group G] (m : G →* Matrix ι ι ℂ)
    (hms : ∀ g, (m g)ᴴ * s * m g = s) (g : G) (x y : EuclideanSpace ℂ ι) :
    omJ (cplx s hs1 hs2) (kM m g x) (kM m g y) = omJ (cplx s hs1 hs2) x y := by
  rw [omJ_cplx, omJ_cplx, crd_kM, crd_kM, form_mulVec, hms]

theorem detPlus_cocycle {s : Matrix ι ι ℂ} (hs1 : sᴴ = s) (hs2 : s * s = 1) {G : Type} [Group G] (m : G →* Matrix ι ι ℂ)
    (hms : ∀ g, (m g)ᴴ * s * m g = s) :
    (∀ g, star (dP s (m g)) * dP s (m g) * lam (kM m g) = 1) ∧
    ∀ g g', dP s (m g) * dP s (m g') * mu (cplx s hs1 hs2) (kM m (g * g')) (kM m g) =
      dP s (m (g * g')) * lam (kM m (g * g')) := by
  obtain ⟨hl, hmu⟩ := GlobalTheory.T.gaussianPairing_unitaryGroup_two_three (EuclideanSpace ℂ ι) ι (crd ι) norm_sq_crd s hs1 hs2 (cplx s hs1 hs2)
    (crd_cplx s hs1 hs2)
  have hk := crd_kM m
  refine ⟨fun g => ?_, fun g g' => ?_⟩
  · obtain ⟨e1, e2, e3⟩ := hl (m g) (kM m g) (hms g) (hk g)
    have : star (dP s (m g)) ≠ 0 := star_ne_zero.2 e1
    rw [e3, e2]
    field_simp
  · obtain ⟨e1, e2, e3⟩ := hl (m (g * g')) (kM m (g * g')) (hms _) (hk _)
    have e4 := (hl (m g) (kM m g) (hms g) (hk g)).1
    have e5 := (hl (m g') (kM m g') (hms g') (hk g')).1
    have : star (dP s (m (g * g'))) ≠ 0 := star_ne_zero.2 e1
    have e6 : (m g)⁻¹ * m (g * g') = m g' := by
      have : m g⁻¹ * m g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rw [Matrix.inv_eq_left_inv this, ← map_mul, inv_mul_cancel_left]
    rw [hmu (m (g * g')) (m g) (kM m (g * g')) (kM m g) (hms _) (hms _) (hk _) (hk _), e3, e2, e6]
    field_simp

theorem exists_osc_bound_deriv : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∃ N : ℕ, ∀ f, Sm ρ f → ∃ C : ℝ, ∀ g, ‖Ω g f‖ ≤ C * (1 + ∑ i, ∑ j, ‖m g i j‖) ^ N) ∧ ∀ (γ : ℝ → G) (X : Matrix ι ι ℂ), γ 0 = 1 → (∀ i j, HasDerivAt (fun t => m (γ t) i j) (X i j) 0) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q → ∃ lam : ℂ, ∀ f, Sm ρ f → HasDerivAt (fun t => Ω (γ t) f) (quad ρ c p q f + lam • f) 0 := by
  intro ι _ _ H h1 h2 B _ _ _ ρ hρ G _ m hm
  obtain ⟨R, s, hR, hs1, hs2, rfl⟩ := GlobalTheory.hermitian_congr_involution ι H h1 h2
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det R).2 hR.isUnit
  have hback : ∀ X : Matrix ι ι ℂ, (u⁻¹).1ᴴ * (u.1ᴴ * X * u.1) * (u⁻¹).1 = X := fun X =>
    calc _ = (u.1 * (u⁻¹).1)ᴴ * X * (u.1 * (u⁻¹).1) := by simp only [mul_assoc, conjTranspose_mul]
      _ = X := by simp
  let E₀ : (ι → ℂ) ≃L[ℝ] (ι → ℂ) := ContinuousLinearEquiv.equivOfInverse (mvL (u⁻¹).1) (mvL u.1)
    (fun v => by simp) fun v => by simp
  let E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) := (crd ι).trans E₀
  have hE : ∀ v, E v = (u⁻¹).1 *ᵥ crd ι v := fun _ => rfl
  have hJ := cplx_cplx s hs1 hs2
  have hEom : ∀ x y, (star (E y) ⬝ᵥ (u.1ᴴ * s * u.1) *ᵥ E x).im = omJ (cplx s hs1 hs2) x y := fun x y => by
    rw [hE, hE, form_mulVec, hback, omJ_cplx]
  have hρ' : IsHeis (omJ (cplx s hs1 hs2)) fun v => ρ (E v) :=
    isHeis_comp hρ (E : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ)) hEom
  let m' : G →* Matrix ι ι ℂ :=
    { toFun := fun g => u.1 * m g * (u⁻¹).1
      map_one' := by simp
      map_mul' := fun g g' => by simp only [map_mul, mul_assoc, Units.inv_mul_cancel_left] }
  have hm' : ∀ g, m' g = u.1 * m g * (u⁻¹).1 := fun _ => rfl
  have hms : ∀ g, (m' g)ᴴ * s * m' g = s := fun g => by
    calc _ = (u⁻¹).1ᴴ * ((m g)ᴴ * (u.1ᴴ * s * u.1) * m g) * (u⁻¹).1 := by
          simp only [hm', mul_assoc, conjTranspose_mul]
      _ = s := by rw [hm, hback]
  have hEk : ∀ (M : Matrix ι ι ℂ) v, E (kL (u.1 * M * (u⁻¹).1) v) = M *ᵥ E v := fun M v => by
    simp only [hE, crd_kL, mulVec_mulVec, mul_assoc, Units.inv_mul_cancel_left]
  have hom := omJ_kM hs1 hs2 m' hms
  have hc1 : (fun g => dP s (m' g)) 1 = 1 := by simp only [map_one, detPlus_one₂]
  obtain ⟨hl, hmu⟩ := detPlus_cocycle hs1 hs2 m' hms
  have hΩ := isOsc_osc (c := fun g => dP s (m' g)) hJ hρ' hom hc1 hl hmu
  have hkM : ∀ g, kM m' g = kL (u.1 * m g * (u⁻¹).1) := fun _ => rfl
  have hΩ' : IsOsc ρ (fun g v => m g *ᵥ v) fun g => osc hρ' hom (fun g => dP s (m' g)) (MonoidHom.id G g) :=
    isOsc_comp E (MonoidHom.id G) (fun g v => by rw [MonoidHom.id_apply, hkM, hEk]) hΩ
  simp only [MonoidHom.id_apply] at hΩ'
  refine ⟨fun g => osc hρ' hom (fun g => dP s (m' g)) g, hΩ',
    ⟨Fintype.card ι, fun f hf => ?_⟩, fun γ X hγ hX κ _ a p q hq => ?_⟩
  · obtain ⟨K, hK0, hK⟩ := norm_osc_le (c := fun g => dP s (m' g)) hJ hρ' hom ((sm_comp_iff E ρ f).2 hf)
    obtain ⟨L, hL⟩ := norm_det_le (sand ((1 / 2 : ℂ) • ((1 + s) * u.1)) (u⁻¹).1)
      (Matrix.of.symm ((1 / 2 : ℂ) • (1 - s)))
    refine ⟨L * K, fun g => (hK g).trans ?_⟩
    rw [mul_right_comm, hm', detPlus_sandwich]
    exact mul_le_mul_of_nonneg_right (hL _) hK0
  · have hkX : HasDerivAt (fun t => kM m' (γ t)) (kL (u.1 * X * (u⁻¹).1)) 0 := hasDerivAt_kL u.1 (u⁻¹).1 hX
    have hcγ : DifferentiableAt ℝ (fun t => dP s (m' (γ t))) 0 := differentiableAt_dP s u.1 (u⁻¹).1 hX
    obtain ⟨l, hl⟩ := hasDerivAt_osc (c := fun g => dP s (m' g)) hJ hρ' hom hc1 γ hγ _ hkX hcγ a _ _
      (isQuadOf_comp E hEom (hEk X) hq)
    refine ⟨l, fun f hf => ?_⟩
    have := hl f ((sm_comp_iff E ρ f).2 hf)
    rwa [quad_comp] at this

end GlobalTheory.Mem.Lift.OscBound

end
