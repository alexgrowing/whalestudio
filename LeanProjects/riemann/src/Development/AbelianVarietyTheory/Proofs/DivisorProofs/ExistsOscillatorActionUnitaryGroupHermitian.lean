import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPairingUnitaryGroupTwoThreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrInvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjEqSelfOfAnnihilated

noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.UnitaryOsc

section Transport

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem sm_comp_iff (E : V ≃L[ℝ] V') (ρ : V' → B →L[ℂ] B) (f : B) : Sm (fun v => ρ (E v)) f ↔ Sm ρ f :=
  E.contDiff_comp_iff (f := fun v => ρ v f)

theorem isHeis_comp {om : V' → V' → ℝ} {om' : V → V → ℝ} {ρ : V' → B →L[ℂ] B} (h : IsHeis om ρ) (E : V →L[ℝ] V')
    (hE : ∀ x y, om (E x) (E y) = om' x y) : IsHeis om' fun v => ρ (E v) :=
  ⟨fun f => by simp only [map_zero, h.1], fun u v f => by simp only [h.2.1, hE, map_add], fun u f => h.2.2.1 _ f,
    fun f => (h.2.2.2 f).comp E.continuous⟩

theorem fderiv_comp_clm {ρ : V' → B →L[ℂ] B} {f : B} (hf : Sm ρ f) (E : V →L[ℝ] V') (z : V) :
    fderiv ℝ (fun v => ρ (E v) f) 0 z = fderiv ℝ (fun v => ρ v f) 0 (E z) := by
  have h1 : DifferentiableAt ℝ (fun v => ρ v f) (E 0) := (ContDiff.differentiable hf (by simp)).differentiableAt
  have h2 := fderiv_comp (0 : V) h1 E.differentiableAt
  rw [E.fderiv, map_zero] at h2
  exact congrArg (fun T : V →L[ℝ] B => T z) h2

theorem isOsc_comp (E : V ≃L[ℝ] V') {ρ : V' → B →L[ℂ] B} {G G' : Type} [Group G] [Group G'] (φ : G →* G')
    {k : G → V' → V'} {k' : G' → V → V} (hk : ∀ g v, E (k' (φ g) v) = k g (E v)) {Ω : G' → B → B}
    (h : IsOsc (fun v => ρ (E v)) k' Ω) : IsOsc ρ k fun g => Ω (φ g) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [sm_comp_iff] at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨fun g => h1 _, fun g => h2 _, fun g => h3 _, fun f hf => ?_, fun g g' f hf => ?_, fun g v f hf => ?_,
    fun g A hA => h7 _ A fun v => hA _, fun H _ _ _ Φ hΦ g => h8 H Φ (fun v => hΦ _) _⟩
  · simp only [map_one, h4 f hf]
  · simp only [map_mul, h5 _ _ f hf]
  · have := h6 (φ g) (E.symm v) f hf
    simpa only [hk, E.apply_symm_apply] using this

end Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem detPlus_conj₂ {a s s' g g' : Matrix ι ι ℂ} (ha : a.det ≠ 0) (hs : a * s = s' * a) (hg : a * g = g' * a) :
    dP s g = dP s' g' := by
  have e : a * ((1 / 2 : ℂ) • ((1 + s) * g) + (1 / 2 : ℂ) • (1 - s)) =
      ((1 / 2 : ℂ) • ((1 + s') * g') + (1 / 2 : ℂ) • (1 - s')) * a := by
    have e1 : a * (s * g) = s' * g' * a := by rw [← mul_assoc, hs, mul_assoc, hg, mul_assoc]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one, hs, hg, e1]
  have := congrArg Matrix.det e
  rw [det_mul, det_mul, mul_comm] at this
  exact mul_right_cancel₀ ha this

theorem detPlus_one₂ (s : Matrix ι ι ℂ) : dP s 1 = 1 := by
  have : (1 / 2 : ℂ) • ((1 + s) * 1) + (1 / 2 : ℂ) • (1 - s) = (1 : Matrix ι ι ℂ) := by
    rw [mul_one]; module
  rw [dP, this, det_one]

theorem continuous_dP (s : Matrix ι ι ℂ) : Continuous (dP s) := by
  unfold dP
  exact Continuous.matrix_det (by fun_prop)

def mvL (g : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin g).restrictScalars ℝ)

omit [DecidableEq ι] in
@[simp] theorem mvL_apply (g : Matrix ι ι ℂ) (v : ι → ℂ) : mvL g v = g *ᵥ v := rfl

omit [DecidableEq ι] in
theorem form_mulVec (H a : Matrix ι ι ℂ) (x y : ι → ℂ) :
    star (a *ᵥ y) ⬝ᵥ H *ᵥ a *ᵥ x = star y ⬝ᵥ (aᴴ * H * a) *ᵥ x := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

def crd (ι : Type) [Fintype ι] : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) := PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => ℂ

omit [DecidableEq ι] in
theorem inner_crd (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫ = (star (crd ι x) ⬝ᵥ crd ι y).re := by
  rw [PiLp.inner_apply, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [crd, mul_comm]

omit [DecidableEq ι] in
theorem norm_sq_crd (x : EuclideanSpace ℂ ι) : ‖x‖ ^ 2 = ∑ i, ‖crd ι x i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq x

def kL (g : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  ((crd ι).symm : (ι → ℂ) →L[ℝ] EuclideanSpace ℂ ι) ∘L mvL g ∘L (crd ι : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ))

omit [DecidableEq ι] in
theorem crd_kL (g : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : crd ι (kL g v) = g *ᵥ crd ι v := by
  simp [kL]

theorem kL_one : kL (1 : Matrix ι ι ℂ) = 1 :=
  ContinuousLinearMap.ext fun v => (crd ι).injective (by rw [crd_kL, one_mulVec]; rfl)

omit [DecidableEq ι] in
theorem kL_mul (g g' : Matrix ι ι ℂ) : kL (g * g') = kL g * kL g' :=
  ContinuousLinearMap.ext fun v => (crd ι).injective (by
    rw [ContinuousLinearMap.mul_apply, crd_kL, crd_kL, crd_kL, mulVec_mulVec])

omit [DecidableEq ι] in
theorem continuous_kL : Continuous (kL : Matrix ι ι ℂ → _) := by
  refine continuous_clm_apply.2 fun v => ?_
  exact (crd ι).symm.continuous.comp (continuous_id.matrix_mulVec continuous_const)

theorem norm_kL {g : Matrix ι ι ℂ} (hg : gᴴ * g = 1) (v : EuclideanSpace ℂ ι) : ‖kL g v‖ = ‖v‖ := by
  have := form_mulVec 1 g (crd ι v) (crd ι v)
  rw [mul_one, hg, one_mulVec, one_mulVec] at this
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_crd, inner_crd, crd_kL, this]

def cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (kL (I • s) : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
      norm_map' := norm_kL (by
        rw [conjTranspose_smul, h1, smul_mul_smul_comm, h2]
        simp) } rfl

theorem crd_cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) (v : EuclideanSpace ℂ ι) :
    crd ι (cplx s h1 h2 v) = I • s *ᵥ crd ι v := by
  rw [← smul_mulVec]
  exact crd_kL (I • s) v

theorem cplx_cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) (v : EuclideanSpace ℂ ι) :
    cplx s h1 h2 (cplx s h1 h2 v) = -v := by
  apply (crd ι).injective
  rw [crd_cplx, crd_cplx, mulVec_smul, mulVec_mulVec, h2, one_mulVec, smul_smul, I_mul_I, map_neg, neg_one_smul]

theorem omJ_cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) (x y : EuclideanSpace ℂ ι) :
    omJ (cplx s h1 h2) x y = (star (crd ι y) ⬝ᵥ s *ᵥ crd ι x).im := by
  rw [omJ_skew (cplx_cplx s h1 h2), omJ, inner_crd, crd_cplx, dotProduct_smul]
  simp

def uGrp (H : Matrix ι ι ℂ) : Subgroup (Matrix ι ι ℂ)ˣ where
  carrier := {g | (g : Matrix ι ι ℂ)ᴴ * H * g = H}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, conjTranspose_mul] at ha hb ⊢
    calc _ = (b : Matrix ι ι ℂ)ᴴ * ((a : Matrix ι ι ℂ)ᴴ * H * a) * b := by simp only [mul_assoc]
      _ = H := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc _ = ((a⁻¹ : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ)ᴴ * ((a : Matrix ι ι ℂ)ᴴ * H * a) * (a⁻¹ : (Matrix ι ι ℂ)ˣ) := by
          rw [ha]
      _ = ((a : Matrix ι ι ℂ) * (a⁻¹ : (Matrix ι ι ℂ)ˣ).1)ᴴ * H * ((a : Matrix ι ι ℂ) * (a⁻¹ : (Matrix ι ι ℂ)ˣ).1) := by
          simp only [mul_assoc, conjTranspose_mul]
      _ = H := by simp

def kU (H : Matrix ι ι ℂ) : uGrp H →* (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) where
  toFun g := kL (g.1 : Matrix ι ι ℂ)
  map_one' := kL_one
  map_mul' _ _ := kL_mul _ _

theorem exists_osc_involution (H : Matrix ι ι ℂ) (h1 : Hᴴ = H) (h2 : H * H = 1) (B : Type) [NormedAddCommGroup B]
    [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B) (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ)
    (G : Type) [Group G] (m : G →* Matrix ι ι ℂ) (hm : ∀ g, (m g)ᴴ * H * m g = H) :
    ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧
      (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧
      ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f →
        (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) →
        Ω g f = dP s (m g) • f := by
  have hJ := cplx_cplx H h1 h2
  have hρ' : IsHeis (omJ (cplx H h1 h2)) fun v => ρ (crd ι v) :=
    isHeis_comp hρ (crd ι : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ)) fun x y => (omJ_cplx H h1 h2 x y).symm
  obtain ⟨hl, hmu⟩ := GlobalTheory.T.gaussianPairing_unitaryGroup_two_three (EuclideanSpace ℂ ι) ι (crd ι) norm_sq_crd H h1 h2 (cplx H h1 h2) (crd_cplx H h1 h2)
  have hom : ∀ (g : uGrp H) x y, omJ (cplx H h1 h2) (kU H g x) (kU H g y) = omJ (cplx H h1 h2) x y := by
    intro g x y
    have hg : (g.1 : Matrix ι ι ℂ)ᴴ * H * g.1 = H := g.2
    rw [omJ_cplx, omJ_cplx]
    change (star (crd ι (kL _ y)) ⬝ᵥ H *ᵥ crd ι (kL _ x)).im = _
    rw [crd_kL, crd_kL, form_mulVec, hg]
  obtain ⟨Ω, hΩ, hc, hv⟩ := GlobalTheory.T.exists_oscillatorAction_of_gaussianPairings (EuclideanSpace ℂ ι) B (cplx H h1 h2) _ hJ hρ' (uGrp H) (kU H)
    (fun g => dP H (g.1 : Matrix ι ι ℂ)) hom (detPlus_one₂ H)
    (fun g => by
      obtain ⟨e1, e2, e3⟩ := hl (g.1 : Matrix ι ι ℂ) (kU H g) g.2 (crd_kL _)
      have : star (dP H (g.1 : Matrix ι ι ℂ)) ≠ 0 := star_ne_zero.2 e1
      rw [e3, e2]
      field_simp)
    (fun g g' => by
      obtain ⟨e1, e2, e3⟩ := hl ((g * g').1 : Matrix ι ι ℂ) (kU H (g * g')) (g * g').2 (crd_kL _)
      have e4 := (hl (g.1 : Matrix ι ι ℂ) (kU H g) g.2 (crd_kL _)).1
      have e5 := (hl (g'.1 : Matrix ι ι ℂ) (kU H g') g'.2 (crd_kL _)).1
      have : star (dP H ((g * g').1 : Matrix ι ι ℂ)) ≠ 0 := star_ne_zero.2 e1
      have e6 : (g.1 : Matrix ι ι ℂ)⁻¹ * ((g * g').1 : Matrix ι ι ℂ) = g'.1 := by
        rw [← Matrix.coe_units_inv, Subgroup.coe_mul, Units.val_mul, Units.inv_mul_cancel_left]
      rw [hmu ((g * g').1 : Matrix ι ι ℂ) (g.1 : Matrix ι ι ℂ) (kU H (g * g')) (kU H g) (g * g').2 g.2 (crd_kL _)
        (crd_kL _), e3, e2, e6]
      field_simp)
  let φ : G →* uGrp H := m.toHomUnits.codRestrict (uGrp H) hm
  have hφ : ∀ g, ((φ g).1 : Matrix ι ι ℂ) = m g := fun _ => rfl
  refine ⟨fun g => Ω (φ g), isOsc_comp (crd ι) φ (fun g v => crd_kL _ v) hΩ, fun g hg f hf => ?_,
    fun hmc f hf => ?_, fun s g hs hpos hsg f hf hD => ?_⟩
  · have : φ g = 1 := Subtype.ext (Units.ext hg)
    simp only [this]
    exact hΩ.2.2.2.1 f ((sm_comp_iff _ _ _).2 hf)
  · exact hc G φ (continuous_kL.comp hmc) ((continuous_dP H).comp hmc) f ((sm_comp_iff _ _ _).2 hf)
  · obtain ⟨a, ha, has⟩ := GlobalTheory.cartanInvolution_conj_of_posDef ι H s h1 h2 hs hpos
    have hdet : a.det ≠ 0 := by
      intro h0
      have e := congrArg Matrix.det ha
      have e' := congrArg Matrix.det h2
      rw [det_mul, h0, mul_zero] at e
      rw [det_mul, ← e, det_one] at e'
      simp at e'
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det a).2 hdet.isUnit
    let a' : uGrp H := ⟨u, ha⟩
    let g₀ : uGrp H := a'⁻¹ * φ g * a'
    have hg₀ : (u : Matrix ι ι ℂ) * g₀.1 = m g * u := by
      have : a' * g₀ = φ g * a' := by simp only [g₀]; group
      exact congrArg (fun x : uGrp H => (x.1 : Matrix ι ι ℂ)) this
    have hcomm : H * (g₀.1 : Matrix ι ι ℂ) = g₀.1 * H := by
      refine (Units.mul_right_inj u).1 ?_
      rw [← mul_assoc, ← mul_assoc, has, hg₀, mul_assoc, hg₀, mul_assoc, has, ← mul_assoc, ← mul_assoc, hsg]
    have hiso : (g₀.1 : Matrix ι ι ℂ)ᴴ * g₀.1 = 1 := by
      have e : (g₀.1 : Matrix ι ι ℂ)ᴴ * H * g₀.1 = H := g₀.2
      rw [mul_assoc, hcomm, ← mul_assoc] at e
      have e' := congrArg (· * H) e
      simpa only [mul_assoc, h2, mul_one] using e'
    let E : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ) := (crd ι : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ)) ∘L kU H a'
    have hE : ∀ z, E z = (u : Matrix ι ι ℂ) *ᵥ crd ι z := fun z => crd_kL _ z
    have hvac := GlobalTheory.RealWeil.proj_eq_self_of_annihilated (EuclideanSpace ℂ ι) B (cplx H h1 h2) _ hJ (hρ'.twist (kU H a') (hom a')) f
      (ContDiff.comp (g := fun v => ρ v f) hf E.contDiff) fun z => by
        have e1 := fderiv_comp_clm hf E z
        have e2 := fderiv_comp_clm hf E (cplx H h1 h2 z)
        have e3 : E (cplx H h1 h2 z) = I • s *ᵥ E z := by
          rw [hE, hE, crd_cplx, mulVec_smul, mulVec_mulVec, mulVec_mulVec, has]
        rw [e3] at e2
        have e4 := hD (E z)
        rw [← e1, ← e2] at e4
        exact e4
    have key := hv a' g₀ (norm_kL hiso) f ((sm_comp_iff _ _ _).2 hf) hvac
    have e : a' * g₀ * a'⁻¹ = φ g := by simp only [g₀]; group
    rw [e, detPlus_conj₂ hdet has hg₀] at key
    exact key

theorem exists_osc : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧ (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧ ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f → (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) → Ω g f = dP s (m g) • f := by
  intro ι _ _ H h1 h2 B _ _ _ ρ hρ G _ m hm
  obtain ⟨R, s₀, hR, hs1, hs2, rfl⟩ := GlobalTheory.hermitian_congr_involution ι H h1 h2
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det R).2 hR.isUnit
  have hback : ∀ X : Matrix ι ι ℂ, (u⁻¹).1ᴴ * (u.1ᴴ * X * u.1) * (u⁻¹).1 = X := fun X =>
    calc _ = (u.1 * (u⁻¹).1)ᴴ * X * (u.1 * (u⁻¹).1) := by simp only [mul_assoc, conjTranspose_mul]
      _ = X := by simp
  let E : (ι → ℂ) ≃L[ℝ] (ι → ℂ) := ContinuousLinearEquiv.equivOfInverse (mvL (u⁻¹).1) (mvL u.1)
    (fun v => by simp) fun v => by simp
  have hE : ∀ v, E v = (u⁻¹).1 *ᵥ v := fun _ => rfl
  have hρ' : IsHeis (fun x y => (star y ⬝ᵥ s₀ *ᵥ x).im) fun v => ρ (E v) :=
    isHeis_comp hρ (E : (ι → ℂ) →L[ℝ] (ι → ℂ)) fun x y => by
      change (star ((u⁻¹).1 *ᵥ y) ⬝ᵥ _ *ᵥ (u⁻¹).1 *ᵥ x).im = _
      rw [form_mulVec, hback]
  let m' : G →* Matrix ι ι ℂ :=
    { toFun := fun g => u.1 * m g * (u⁻¹).1
      map_one' := by simp
      map_mul' := fun g g' => by simp only [map_mul, mul_assoc, Units.inv_mul_cancel_left] }
  have hm' : ∀ g, m' g = u.1 * m g * (u⁻¹).1 := fun _ => rfl
  obtain ⟨Ω, hΩ, ho, hc, hv⟩ := exists_osc_involution s₀ hs1 hs2 B _ hρ' G m' fun g => by
    calc _ = (u⁻¹).1ᴴ * ((m g)ᴴ * (u.1ᴴ * s₀ * u.1) * m g) * (u⁻¹).1 := by
          simp only [hm', mul_assoc, conjTranspose_mul]
      _ = s₀ := by rw [hm, hback]
  refine ⟨Ω, isOsc_comp E (MonoidHom.id G) (fun g v => ?_) hΩ, fun g hg f hf => ?_, fun hmc f hf => ?_,
    fun s g hs hpos hsg f hf hD => ?_⟩
  · simp only [hE, hm', MonoidHom.id_apply, mulVec_mulVec, mul_assoc, Units.inv_mul_cancel_left]
  · exact ho g (by simp [hm', hg]) f ((sm_comp_iff _ _ _).2 hf)
  · exact hc ((continuous_const.mul hmc).mul continuous_const) f ((sm_comp_iff _ _ _).2 hf)
  · have hpos' : (s₀ * (u.1 * s * (u⁻¹).1)).PosDef := by
      have := hpos.conjTranspose_mul_mul_same (B := (u⁻¹).1) (Matrix.mulVec_injective_of_isUnit (u⁻¹).isUnit)
      have e : s₀ * (u.1 * s * (u⁻¹).1) = (u⁻¹).1ᴴ * (u.1ᴴ * s₀ * u.1 * s) * (u⁻¹).1 := by
        calc _ = (u.1 * (u⁻¹).1)ᴴ * (s₀ * (u.1 * s * (u⁻¹).1)) := by simp
          _ = _ := by simp only [mul_assoc, conjTranspose_mul]
      rw [e]
      exact this
    have key := hv (u.1 * s * (u⁻¹).1) g
      (by simp only [mul_assoc, Units.inv_mul_cancel_left]; rw [← mul_assoc s, hs, one_mul, Units.mul_inv]) hpos'
      (by simp only [hm', mul_assoc, Units.inv_mul_cancel_left]; rw [← mul_assoc s, hsg, mul_assoc]) f
      ((sm_comp_iff _ _ _).2 hf) fun z => by
        have e1 := fderiv_comp_clm hf (E : (ι → ℂ) →L[ℝ] (ι → ℂ)) z
        have e2 := fderiv_comp_clm hf (E : (ι → ℂ) →L[ℝ] (ι → ℂ)) (I • (u.1 * s * (u⁻¹).1) *ᵥ z)
        have e3 : E (I • (u.1 * s * (u⁻¹).1) *ᵥ z) = I • s *ᵥ E z := by
          simp only [hE, mulVec_smul, mulVec_mulVec, mul_assoc, Units.inv_mul_cancel_left]
        simp only [ContinuousLinearEquiv.coe_coe] at e1 e2
        rw [e1, e2, e3]
        exact hD _
    rw [key, ← detPlus_conj₂ (s := s) (g := m g) hR (by simp) (by simp [hm'])]

end GlobalTheory.RealWeil.UnitaryOsc

end
