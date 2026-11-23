import Mathlib

noncomputable section

open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

abbrev L2 (l : Type) [Fintype l] : Type := Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ l))

abbrev Sch (l : Type) [Fintype l] : Type := 𝓢(EuclideanSpace ℝ l, ℂ)

def pPart (w : l ⊕ l → ℝ) : EuclideanSpace ℝ l := WithLp.toLp 2 fun i => w (Sum.inl i)

def qPart (w : l ⊕ l → ℝ) : EuclideanSpace ℝ l := WithLp.toLp 2 fun i => w (Sum.inr i)

def sympl (w w' : l ⊕ l → ℝ) : ℝ := ⟪pPart w, qPart w'⟫ - ⟪qPart w, pPart w'⟫

def phase (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) : ℂ :=
  exp (((2 * π * ⟪qPart w, x⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I)

def rhoFun (w : l ⊕ l → ℝ) (f : EuclideanSpace ℝ l → ℂ) : EuclideanSpace ℝ l → ℂ :=
  fun x => phase w x * f (x + pPart w)

omit [Fintype l] in
theorem pPart_add (w w' : l ⊕ l → ℝ) : pPart (w + w') = pPart w + pPart w' := rfl

omit [Fintype l] in
theorem qPart_add (w w' : l ⊕ l → ℝ) : qPart (w + w') = qPart w + qPart w' := rfl

omit [Fintype l] in
theorem pPart_smul (t : ℝ) (w : l ⊕ l → ℝ) : pPart (t • w) = t • pPart w := rfl

omit [Fintype l] in
theorem qPart_smul (t : ℝ) (w : l ⊕ l → ℝ) : qPart (t • w) = t • qPart w := rfl

theorem norm_phase (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) : ‖phase w x‖ = 1 :=
  norm_exp_ofReal_mul_I _

theorem continuous_phase (w : l ⊕ l → ℝ) : Continuous (phase w) := by
  unfold phase
  fun_prop

theorem rhoFun_rhoFun (w w' : l ⊕ l → ℝ) (f : EuclideanSpace ℝ l → ℂ) :
    rhoFun w (rhoFun w' f) = exp (((π * sympl w w' : ℝ) : ℂ) * I) • rhoFun (w + w') f := by
  funext x
  simp only [rhoFun, phase, Pi.smul_apply, smul_eq_mul, pPart_add, qPart_add, ← mul_assoc, ← Complex.exp_add,
    add_assoc x]
  congr 2
  rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
  congr 2
  simp only [sympl, inner_add_left, inner_add_right, real_inner_comm (pPart w) (qPart w'),
    real_inner_comm (qPart w) (pPart w')]
  ring

theorem rhoFun_zero (f : EuclideanSpace ℝ l → ℂ) : rhoFun 0 f = f := by
  funext x
  have h1 : pPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have h2 : qPart (0 : l ⊕ l → ℝ) = 0 := rfl
  simp [rhoFun, phase, h1, h2]

theorem rhoFun_congr (w : l ⊕ l → ℝ) {f g : EuclideanSpace ℝ l → ℂ} (h : f =ᵐ[volume] g) :
    rhoFun w f =ᵐ[volume] rhoFun w g := by
  filter_upwards [(measurePreserving_add_right volume (pPart w)).quasiMeasurePreserving.ae_eq_comp h] with x hx
  simp only [rhoFun]
  rw [show f (x + pPart w) = g (x + pPart w) from hx]

theorem eLpNorm_rhoFun (w : l ⊕ l → ℝ) (f : L2 l) : eLpNorm (rhoFun w f) 2 volume = eLpNorm f 2 volume := by
  rw [← eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) (measurePreserving_add_right volume (pPart w))]
  refine eLpNorm_congr_norm_ae (.of_forall fun x => ?_)
  simp [rhoFun, norm_phase]

theorem memLp_rhoFun (w : l ⊕ l → ℝ) (f : L2 l) : MemLp (rhoFun w f) 2 volume :=
  ⟨(continuous_phase w).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).comp_measurePreserving (measurePreserving_add_right volume (pPart w))),
    by rw [eLpNorm_rhoFun]; exact Lp.eLpNorm_lt_top f⟩

def rhoIsometry (w : l ⊕ l → ℝ) : L2 l →ₗᵢ[ℂ] L2 l where
  toFun f := (memLp_rhoFun w f).toLp
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ((rhoFun_congr w (Lp.coeFn_add f g)).trans (.of_forall fun x => ?_))
    simp [rhoFun, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ((rhoFun_congr w (Lp.coeFn_smul c f)).trans (.of_forall fun x => ?_))
    simp [rhoFun, mul_left_comm]
  norm_map' f := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Lp.norm_toLp, eLpNorm_rhoFun, Lp.norm_def]

theorem coeFn_rhoIsometry (w : l ⊕ l → ℝ) (f : L2 l) : rhoIsometry w f =ᵐ[volume] rhoFun w f :=
  (memLp_rhoFun w f).coeFn_toLp

theorem rhoIsometry_rhoIsometry (w w' : l ⊕ l → ℝ) (f : L2 l) :
    rhoIsometry w (rhoIsometry w' f) = exp (((π * sympl w w' : ℝ) : ℂ) * I) • rhoIsometry (w + w') f := by
  refine Lp.ext ((coeFn_rhoIsometry _ _).trans ((rhoFun_congr w (coeFn_rhoIsometry _ _)).trans ?_))
  rw [rhoFun_rhoFun]
  filter_upwards [Lp.coeFn_smul (exp (((π * sympl w w' : ℝ) : ℂ) * I)) (rhoIsometry (w + w') f),
    coeFn_rhoIsometry (w + w') f] with x h1 h2
  rw [h1, Pi.smul_apply, Pi.smul_apply, h2]

theorem rhoIsometry_zero (f : L2 l) : rhoIsometry 0 f = f :=
  Lp.ext ((coeFn_rhoIsometry _ _).trans (by rw [rhoFun_zero]))

def rho (w : l ⊕ l → ℝ) : L2 l ≃ₗᵢ[ℂ] L2 l :=
  LinearIsometryEquiv.ofSurjective (rhoIsometry w) fun f =>
    ⟨(exp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹ • rhoIsometry (-w) f, by
      rw [map_smul, rhoIsometry_rhoIsometry, add_neg_cancel, rhoIsometry_zero, inv_smul_smul₀ (exp_ne_zero _)]⟩

theorem coeFn_rho (w : l ⊕ l → ℝ) (f : L2 l) : rho w f =ᵐ[volume] rhoFun w f := coeFn_rhoIsometry w f

theorem rho_rho (w w' : l ⊕ l → ℝ) (f : L2 l) :
    rho w (rho w' f) = exp (((π * sympl w w' : ℝ) : ℂ) * I) • rho (w + w') f := rhoIsometry_rhoIsometry w w' f

theorem rho_zero (f : L2 l) : rho 0 f = f := rhoIsometry_zero f

def dRho (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l :=
  lineDerivOpCLM ℂ (Sch l) (pPart w) +
    (2 * π * I : ℂ) • smulLeftCLM ℂ fun x : EuclideanSpace ℝ l => ((⟪qPart w, x⟫ : ℝ) : ℂ)

theorem dRho_apply (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) :
    dRho w f x = fderiv ℝ f x (pPart w) + 2 * π * I * (⟪qPart w, x⟫ : ℝ) * f x := by
  have h : (fun x : EuclideanSpace ℝ l => ((⟪qPart w, x⟫ : ℝ) : ℂ)).HasTemperateGrowth :=
    (ofRealCLM.comp (innerSL ℝ (qPart w))).hasTemperateGrowth
  simp [dRho, h, lineDerivOp_apply_eq_fderiv, mul_assoc]

theorem hasDerivAt_rhoFun (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) :
    HasDerivAt (fun t : ℝ => rhoFun (t • w) f x) (dRho w f x) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * π * (t * ⟪qPart w, x⟫) + π * (t * (t * ⟪pPart w, qPart w⟫)))
      (2 * π * ⟪qPart w, x⟫) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const ⟪qPart w, x⟫).const_mul (2 * π)).add
      (((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).mul_const ⟪pPart w, qPart w⟫)).const_mul π)
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.mul_const I).cexp
  have h3 : HasDerivAt (fun t : ℝ => x + t • pPart w) (pPart w) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (pPart w)).const_add x
  have h4 : HasDerivAt (fun t : ℝ => f (x + t • pPart w)) (fderiv ℝ f x (pPart w)) 0 := by
    have := (f.hasFDerivAt (x + (0 : ℝ) • pPart w)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul h4
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => ?_)
  · rw [dRho_apply]
    simp
    ring
  · simp only [rhoFun, phase, pPart_smul, qPart_smul, real_inner_smul_left, real_inner_smul_right, Pi.mul_apply]

theorem dRho_add (w w' : l ⊕ l → ℝ) : dRho (w + w') = dRho w + dRho w' := by
  ext f x
  simp only [ContinuousLinearMap.add_apply, SchwartzMap.add_apply, dRho_apply, pPart_add, qPart_add, inner_add_left,
    map_add, ofReal_add]
  ring

theorem dRho_smul (t : ℝ) (w : l ⊕ l → ℝ) : dRho (t • w) = (t : ℂ) • dRho w := by
  ext f x
  simp only [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, dRho_apply, pPart_smul, qPart_smul,
    real_inner_smul_left, map_smul, ofReal_mul, smul_eq_mul, real_smul]
  ring

theorem dRho_comm (w w' : l ⊕ l → ℝ) :
    dRho w * dRho w' - dRho w' * dRho w = (2 * π * I * sympl w w' : ℂ) • (1 : Sch l →L[ℂ] Sch l) := by
  have key : ∀ (u v : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l), fderiv ℝ (dRho v f) x (pPart u) =
      fderiv ℝ (fderiv ℝ f) x (pPart u) (pPart v) + (2 * π * I * (⟪qPart v, pPart u⟫ : ℝ) * f x +
        2 * π * I * (⟪qPart v, x⟫ : ℝ) * fderiv ℝ f x (pPart u)) := by
    intro u v f x
    have e : ⇑(dRho v f) = fun y => fderiv ℝ f y (pPart v) + 2 * π * I * (⟪qPart v, y⟫ : ℝ) * f y :=
      funext (dRho_apply v f)
    have d1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      (fderivCLM ℂ _ _ f).differentiableAt.hasFDerivAt
    have d2 := d1.clm_apply (hasFDerivAt_const (pPart v) x)
    have d3 := ((ofRealCLM.comp (innerSL ℝ (qPart v))).hasFDerivAt (x := x)).const_mul (2 * π * I : ℂ)
    have d4 := d2.add (d3.mul (f.hasFDerivAt x))
    rw [e]
    refine (congrArg (fun L : EuclideanSpace ℝ l →L[ℝ] ℂ => L (pPart u)) d4.fderiv).trans ?_
    simp
    ring
  ext f x
  have hs : fderiv ℝ (fderiv ℝ f) x (pPart w) (pPart w') = fderiv ℝ (fderiv ℝ f) x (pPart w') (pPart w) :=
    ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, SchwartzMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, SchwartzMap.smul_apply, smul_eq_mul]
  rw [dRho_apply w (dRho w' f), dRho_apply w' (dRho w f), key, key, dRho_apply, dRho_apply, hs]
  simp only [sympl, real_inner_comm (pPart w) (qPart w'), ofReal_sub]
  ring

variable [DecidableEq l]

def quad (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Sch l →L[ℂ] Sch l :=
  (4 * π * I : ℂ)⁻¹ • ∑ a, ∑ b, (((X * Matrix.J l ℝ) a b / 2 : ℝ) : ℂ) •
    (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1))

theorem mul_J_symm {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) :
    (X * Matrix.J l ℝ)ᵀ = X * Matrix.J l ℝ := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have h2 := congrArg (fun Y => Matrix.J l ℝ * Y * Matrix.J l ℝ) h
  simp only [Matrix.mul_assoc, J_squared] at h2
  simp only [← Matrix.mul_assoc, J_squared] at h2
  rw [transpose_mul, J_transpose]
  simpa using h2

theorem dRho_eq_sum (w : l ⊕ l → ℝ) : dRho w = ∑ a, (w a : ℂ) • dRho (Pi.single a 1) := by
  let L : (l ⊕ l → ℝ) →+ (Sch l →L[ℂ] Sch l) := AddMonoidHom.mk' dRho dRho_add
  have : w = ∑ a, w a • (Pi.single a 1 : l ⊕ l → ℝ) := by
    ext b
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  exact (map_sum L _ _).trans (Finset.sum_congr rfl fun a _ => dRho_smul _ _)

theorem sympl_single (b : l ⊕ l) (u : l ⊕ l → ℝ) : sympl (Pi.single b 1) u = -(Matrix.J l ℝ *ᵥ u) b := by
  rcases b with b | b <;>
    simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]

theorem quad_comm {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (u : l ⊕ l → ℝ) :
    quad X * dRho u - dRho u * quad X = dRho (X *ᵥ u) := by
  set S := X * Matrix.J l ℝ with hS
  have hsym : ∀ a b, S a b = S b a := fun a b => (congrFun (congrFun (mul_J_symm hX) b) a)
  set s : l ⊕ l → ℝ := fun b => sympl (Pi.single b 1) u with hs
  have hXu : ∀ a, (X *ᵥ u) a = ∑ b, S a b * s b := by
    intro a
    have : X *ᵥ u = S *ᵥ (-(Matrix.J l ℝ *ᵥ u)) := by
      rw [mulVec_neg, mulVec_mulVec, hS, Matrix.mul_assoc, J_squared]
      simp [neg_mulVec]
    rw [this]
    simp only [hs, sympl_single]
    rfl
  set D : l ⊕ l → (Sch l →L[ℂ] Sch l) := fun a => dRho (Pi.single a 1) with hD
  have hc : ∀ a, D a * dRho u = dRho u * D a + (2 * π * I * s a : ℂ) • 1 := fun a => by
    rw [← dRho_comm]
    simp [hD]
  have h2 : ∀ a b, (D a * D b + D b * D a) * dRho u - dRho u * (D a * D b + D b * D a) =
      (4 * π * I : ℂ) • ((s b : ℂ) • D a + (s a : ℂ) • D b) := fun a b => by
    have e : ∀ a b, D a * D b * dRho u = dRho u * (D a * D b) +
        ((2 * π * I * s a : ℂ) • D b + (2 * π * I * s b : ℂ) • D a) := fun a b => by
      rw [mul_assoc, hc b, mul_add, ← mul_assoc, hc a, add_mul, mul_assoc, add_assoc]
      simp
    rw [add_mul, e, e, mul_add]
    module
  have hne : (4 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : quad X * dRho u - dRho u * quad X =
      ∑ a, ∑ b, ((S a b / 2 : ℝ) : ℂ) • ((s b : ℂ) • D a + (s a : ℂ) • D b) := by
    simp only [quad, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      ← Finset.sum_sub_distrib]
    rw [inv_smul_eq_iff₀ hne]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm (4 * π * I : ℂ), ← h2]
  rw [h3, dRho_eq_sum (X *ᵥ u)]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => ((S a b / 2 : ℝ) : ℂ) • (s a : ℂ) • D b), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hXu, ← Finset.sum_add_distrib, ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hsym b a]
  push_cast
  module

theorem dRho_single_inl (j : l) (f : Sch l) :
    dRho (Pi.single (Sum.inl j) 1) f = ∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)} f := by
  have h1 : pPart (Pi.single (Sum.inl j) 1 : l ⊕ l → ℝ) = EuclideanSpace.single j 1 := by
    ext i
    simp [pPart, Pi.single_apply]
  have h2 : qPart (Pi.single (Sum.inl j) 1 : l ⊕ l → ℝ) = 0 := by
    ext i
    simp [qPart]
  ext x
  simp [dRho_apply, h1, h2, lineDerivOp_apply_eq_fderiv]

theorem dRho_single_inr (k : l) (f : Sch l) (x : EuclideanSpace ℝ l) :
    dRho (Pi.single (Sum.inr k) 1) f x = 2 * π * I * x k * f x := by
  have h1 : pPart (Pi.single (Sum.inr k) 1 : l ⊕ l → ℝ) = 0 := by
    ext i
    simp [pPart]
  have h2 : qPart (Pi.single (Sum.inr k) 1 : l ⊕ l → ℝ) = EuclideanSpace.single k 1 := by
    ext i
    simp [qPart, Pi.single_apply]
  simp [dRho_apply, h1, h2, EuclideanSpace.inner_single_left]

theorem quad_fromBlocks {A B C D : Matrix l l ℝ} (hX : fromBlocks A B C D ∈ LieAlgebra.Symplectic.sp l ℝ)
    (f : Sch l) (x : EuclideanSpace ℝ l) :
    quad (fromBlocks A B C D) f x =
      (4 * π * I : ℂ)⁻¹ * ∑ j, ∑ k, (B j k : ℂ) * (∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)}
          (∂_{(EuclideanSpace.single k 1 : EuclideanSpace ℝ l)} f)) x
        - ∑ j, ∑ k, (A j k : ℂ) * x k * (∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)} f) x
        - (A.trace : ℝ) / 2 * f x - π * I * ∑ j, ∑ k, (C j k : ℂ) * x j * x k * f x := by
  have hS : fromBlocks A B C D * Matrix.J l ℝ = fromBlocks B (-A) D (-C) := by
    simp [Matrix.J, fromBlocks_multiply]
  have hsym := mul_J_symm hX
  rw [hS] at hsym
  have hD : ∀ j k, D j k = -A k j := fun j k => congrFun (congrFun hsym (Sum.inl k)) (Sum.inr j)
  have hne : (4 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  set P : l → (Sch l →L[ℂ] Sch l) := fun j => dRho (Pi.single (Sum.inl j) 1) with hP
  set Q : l → (Sch l →L[ℂ] Sch l) := fun j => dRho (Pi.single (Sum.inr j) 1) with hQ
  have hPP : ∀ j k, P k * P j = P j * P k := fun j k => by
    have := dRho_comm (l := l) (Pi.single (Sum.inl k) 1) (Pi.single (Sum.inl j) 1)
    rw [sympl_single] at this
    rw [← sub_eq_zero, this]
    simp [Matrix.J]
  have hPQ : ∀ j k, P j * Q k = Q k * P j + (2 * π * I * (if j = k then 1 else 0) : ℂ) • 1 := fun j k => by
    have := dRho_comm (l := l) (Pi.single (Sum.inl j) 1) (Pi.single (Sum.inr k) 1)
    rw [sympl_single] at this
    rw [← sub_eq_iff_eq_add', this]
    by_cases h : j = k <;> simp [Matrix.J, h, Matrix.one_apply]
  have hQa : ∀ k (g : Sch l), Q k g x = 2 * π * I * x k * g x := fun k g => dRho_single_inr k g x
  have hq : quad (fromBlocks A B C D) = (4 * π * I : ℂ)⁻¹ • ((∑ j, ∑ k, (B j k : ℂ) • (P j * P k)) -
      (∑ j, ∑ k, (2 * A j k : ℂ) • (Q k * P j)) - (2 * π * I * (A.trace : ℝ) : ℂ) • 1 -
      ∑ j, ∑ k, (C j k / 2 : ℂ) • (Q j * Q k + Q k * Q j)) := by
    rw [quad, hS]
    congr 1
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.neg_apply, hD]
    have t : (2 * π * I * (A.trace : ℝ) : ℂ) • (1 : Sch l →L[ℂ] Sch l) =
        ∑ j, ∑ k, (A j k : ℂ) • (2 * π * I * (if j = k then 1 else 0) : ℂ) • (1 : Sch l →L[ℂ] Sch l) := by
      simp only [Matrix.trace, diag_apply, ofReal_sum, Finset.mul_sum, Finset.sum_smul, smul_smul, mul_ite, mul_one,
        mul_zero, ite_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
    rw [t, Finset.sum_comm (f := fun j k => ((-A k j / 2 : ℝ) : ℂ) • _)]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    change ((B j k / 2 : ℝ) : ℂ) • (P j * P k + P k * P j) + ((-A j k / 2 : ℝ) : ℂ) • (Q k * P j + P j * Q k) +
      (((-A j k / 2 : ℝ) : ℂ) • (P j * Q k + Q k * P j) + ((-C j k / 2 : ℝ) : ℂ) • (Q j * Q k + Q k * Q j)) = _
    rw [hPP j k, hPQ j k]
    push_cast
    module
  rw [hq]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
    SchwartzMap.smul_apply, SchwartzMap.sub_apply, SchwartzMap.add_apply, SchwartzMap.sum_apply, smul_eq_mul, hQa]
  simp only [hP, dRho_single_inl, mul_sub, Finset.mul_sum]
  congr 1
  · congr 1
    · congr 1
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      field_simp
      ring
    · field_simp
      ring
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    field_simp
    ring

end GlobalTheory.RealWeil

namespace GlobalTheory.Published

open GlobalTheory.RealWeil

def RealMetaplecticRepresentation : Prop :=
  ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l],
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)),
      (IsCoveringMap pr ∧ Function.Surjective pr ∧
        ∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧
      (∀ f : L2 l, Continuous fun g => om g f) ∧
      (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
        om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧
      (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧
      (∀ (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
        (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
        ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2)) ∧
      (∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
        (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) ∧
        ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((quad X f).toLp 2) 0)

end GlobalTheory.Published

end
