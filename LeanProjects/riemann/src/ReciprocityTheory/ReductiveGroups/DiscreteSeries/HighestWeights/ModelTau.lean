import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelInner
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGen

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def tauL (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : MV ε m →ₗ[ℂ] MV ε m where
  toFun f := MV.mk (rtr ε k f.fn) (rtr_mem ε m k f.mem)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tauC (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : MV ε m →L[ℂ] MV ε m :=
  LinearMap.toContinuousLinearMap (tauL ε m k)

@[simp] theorem tauC_fn (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) (f : MV ε m) :
    (tauC ε m k f).fn = rtr ε k f.fn := rfl

theorem tauC_one (ε : Fin n → Bool) (m : Fin n → ℤ) : tauC ε m 1 = 1 := by
  refine ContinuousLinearMap.ext fun f => MV.ext ?_
  rw [tauC_fn, rtr_one]
  rfl

theorem tauC_mul (ε : Fin n → Bool) (m : Fin n → ℤ) (k₁ k₂ : KG ε) :
    tauC ε m (k₁ * k₂) = tauC ε m k₁ * tauC ε m k₂ := by
  refine ContinuousLinearMap.ext fun f => MV.ext ?_
  rw [tauC_fn, rtr_mul, ContinuousLinearMap.mul_apply, tauC_fn, tauC_fn]

theorem tauC_inner (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) (f g : MV ε m) :
    inner ℂ (tauC ε m k f) (tauC ε m k g) = inner ℂ f g := by
  show mvInner _ _ = mvInner _ _
  unfold mvInner
  simp only [tauC_fn]
  haveI := muK_rightInvariant ε
  exact MeasureTheory.integral_mul_right_eq_self (fun x => starRingEnd ℂ (f.fn x) * g.fn x) k

theorem tauC_mem_unitary (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : tauC ε m k ∈ unitary (MV ε m →L[ℂ] MV ε m) := by
  have hinv : ∀ f, tauC ε m k (tauC ε m k⁻¹ f) = f := by
    intro f
    rw [← ContinuousLinearMap.mul_apply, ← tauC_mul, mul_inv_cancel, tauC_one]
    rfl
  have hinv' : ∀ f, tauC ε m k⁻¹ (tauC ε m k f) = f := by
    intro f
    rw [← ContinuousLinearMap.mul_apply, ← tauC_mul, inv_mul_cancel, tauC_one]
    rfl
  have hadj : star (tauC ε m k) = tauC ε m k⁻¹ := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [← tauC_inner ε m k (tauC ε m k⁻¹ x) y, hinv]
  first
    | rw [Unitary.mem_iff, hadj]
    | rw [unitary.mem_iff, hadj]
  constructor
  · ext f
    rw [ContinuousLinearMap.mul_apply, hinv', ContinuousLinearMap.one_apply]
  · ext f
    rw [ContinuousLinearMap.mul_apply, hinv, ContinuousLinearMap.one_apply]

def mvFnL (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m →ₗ[ℂ] (KG ε → ℂ) where
  toFun f := f.fn
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mvFnL_injective (ε : Fin n → Bool) (m : Fin n → ℤ) : Function.Injective (mvFnL ε m) := fun _ _ h => MV.ext h

theorem continuous_tauC_apply (ε : Fin n → Bool) (m : Fin n → ℤ) (f : MV ε m) :
    Continuous fun k : KG ε => tauC ε m k f := by
  let e := (LinearEquiv.ofInjective (mvFnL ε m) (mvFnL_injective ε m)).toContinuousLinearEquiv
  have h : Continuous fun k : KG ε => e (tauC ε m k f) := by
    refine continuous_induced_rng.2 ?_
    have hfun : (fun k : KG ε => ((e (tauC ε m k f) : LinearMap.range (mvFnL ε m)) : KG ε → ℂ)) =
        fun k x => f.fn (x * k) := rfl
    rw [Function.comp_def, hfun]
    exact continuous_pi fun x => (continuous_of_mem_Vsp ε m f.mem).comp (continuous_const.mul continuous_id)
  have h2 : (fun k : KG ε => tauC ε m k f) = fun k => e.symm (e (tauC ε m k f)) := by
    funext k; simp
  rw [h2]
  exact e.symm.continuous.comp h

theorem continuous_tauC (ε : Fin n → Bool) (m : Fin n → ℤ) : Continuous (tauC ε m) :=
  continuous_clm_apply.2 (continuous_tauC_apply ε m)

def tauM (ε : Fin n → Bool) (m : Fin n → ℤ) : KG ε →* unitary (MV ε m →L[ℂ] MV ε m) where
  toFun k := ⟨tauC ε m k, tauC_mem_unitary ε m k⟩
  map_one' := Subtype.ext (tauC_one ε m)
  map_mul' k₁ k₂ := Subtype.ext (tauC_mul ε m k₁ k₂)

theorem tauM_coe (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) :
    ((tauM ε m k : unitary (MV ε m →L[ℂ] MV ε m)) : MV ε m →L[ℂ] MV ε m) = tauC ε m k := rfl

theorem continuous_tauM (ε : Fin n → Bool) (m : Fin n → ℤ) : Continuous (tauM ε m) := continuous_induced_rng.2 (continuous_tauC ε m)

private theorem derOp_fn_eq_deriv_kcurve (ε : Fin n → Bool) (m : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (f : MV ε m)
    (x : KG ε) : (derOp ε (tauM ε m) X f).fn x = deriv (fun t : ℝ => f.fn (x * kcurve ε X t)) 0 := by
  by_cases hX : inK ε X
  · have h := derOp_hasDeriv ε (tauM ε m) (continuous_tauM ε m) X hX (kcurve ε X) (kcurve_spec ε hX).2.1
    let evx : MV ε m →ₗ[ℂ] ℂ :=
      { toFun := fun g => g.fn x
        map_add' := fun a b => by simp
        map_smul' := fun c a => by simp }
    let E : (MV ε m →L[ℂ] MV ε m) →L[ℂ] ℂ :=
      (LinearMap.toContinuousLinearMap evx).comp (ContinuousLinearMap.apply ℂ (MV ε m) f)
    have h2 := (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    have h3 : HasDerivAt (fun t : ℝ => f.fn (x * kcurve ε X t)) ((derOp ε (tauM ε m) X f).fn x) 0 := h2
    exact h3.deriv.symm
  · have hk : kcurve ε X = fun _ => 1 := by
      unfold kcurve
      rw [dif_neg hX]
    simp [derOp, hk]

theorem derOp_fn (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (f : MV ε m)
    (x : KG ε) : (derOp ε (tauM ε m) X f).fn x = deriv (fun t : ℝ => f.fn (x * kcurve ε X t)) 0 := by
  exact derOp_fn_eq_deriv_kcurve ε m X f x

theorem inK_add' (ε : Fin n → Bool) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    inK ε (X + Y) := by
  obtain ⟨h1, h2⟩ := hX
  obtain ⟨h3, h4⟩ := hY
  refine ⟨?_, ?_⟩
  · unfold inG at h1 h3 ⊢
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Jm ε + Yᴴ * Jm ε + (Jm ε * X + Jm ε * Y)
        = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
      _ = 0 := by rw [h1, h3, add_zero]
  · rw [Matrix.add_mul, Matrix.mul_add, h2, h4]

theorem inK_rsmul' (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (r : ℝ) :
    inK ε ((r : ℂ) • X) := by
  obtain ⟨h1, h2⟩ := hX
  refine ⟨?_, ?_⟩
  · unfold inG at h1 ⊢
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, h2]

theorem derOp_fn_eq (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (f : MV ε m) (x : KG ε) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Differentiable ℂ F)
    (hfF : ∀ k, f.fn k = F (toMK k)) :
    (derOp ε (tauM ε m) X f).fn x = fderiv ℂ F (toMK x) (toMK x * X) := by
  rw [derOp_fn ε m hX f x]
  exact (hasDerivAt_of_mem_Vsp ε m f.mem hF hfF hX x).deriv

theorem rLinOnK_derOp (ε : Fin n → Bool) (m : Fin n → ℤ) : RLinOnK ε (derOp ε (tauM ε m)) := by
  intro X Y r hX hY
  constructor
  · refine ContinuousLinearMap.ext fun f => MV.ext (funext fun x => ?_)
    obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m f.mem
    rw [_root_.add_apply, MV.fn_add, Pi.add_apply, derOp_fn_eq ε m (inK_add' ε hX hY) f x hF hfF,
      derOp_fn_eq ε m hX f x hF hfF, derOp_fn_eq ε m hY f x hF hfF, Matrix.mul_add, map_add]
  · refine ContinuousLinearMap.ext fun f => MV.ext (funext fun x => ?_)
    obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m f.mem
    rw [_root_.smul_apply, MV.fn_smul, Pi.smul_apply, smul_eq_mul,
      derOp_fn_eq ε m (inK_rsmul' ε hX r) f x hF hfF, derOp_fn_eq ε m hX f x hF hfF, Matrix.mul_smul, map_smul,
      smul_eq_mul]

def dTau (ε : Fin n → Bool) (m : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (MV ε m →L[ℂ] MV ε m) :=
  cextL ε (derOp ε (tauM ε m)) (rLinOnK_derOp ε m)

theorem dTau_fn (ε : Fin n → Bool) (m : Fin n → ℤ) (Z : Matrix (Fin n) (Fin n) ℂ) (f : MV ε m) (x : KG ε) :
    (dTau ε m Z f).fn x = rdc ε Z f.fn x := by
  unfold dTau
  rw [cextL_apply]
  unfold cext
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, MV.fn_add, MV.fn_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, derOp_fn_eq_deriv_kcurve]
  rfl

theorem hasDeriv_dTau (ε : Fin n → Bool) (m : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) :
    HasDerivAt (fun t => ((tauM ε m (γ t) : unitary (MV ε m →L[ℂ] MV ε m)) : MV ε m →L[ℂ] MV ε m))
      (dTau ε m X) 0 := by
  have h := derOp_hasDeriv ε (tauM ε m) (continuous_tauM ε m) X hX γ hγ
  have he : dTau ε m X = derOp ε (tauM ε m) X := by
    unfold dTau
    rw [cextL_apply, cext_of_inK _ (rLinOnK_derOp ε m) hX]
  rw [he]
  exact h

def w0 (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m := MV.mk (f0K ε m) (highest_weight_fn_mem_space ε m)

def wN (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m := ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) • w0 ε m

theorem highest_weight_vector_ne_zero (ε : Fin n → Bool) (m : Fin n → ℤ) : w0 ε m ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : MV ε m => f.fn 1) h
  simp only [MV.fn_zero, Pi.zero_apply] at h1
  have h2 : (w0 ε m).fn 1 = 1 := highest_weight_fn_K_one ε m
  rw [h2] at h1
  exact one_ne_zero h1

theorem norm_wN (ε : Fin n → Bool) (m : Fin n → ℤ) : ‖wN ε m‖ = 1 := by
  have h0 : ‖w0 ε m‖ ≠ 0 := norm_ne_zero_iff.mpr (highest_weight_vector_ne_zero ε m)
  unfold wN
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ h0]

theorem derived_action_weight_vector (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) :
    dTau ε m (Matrix.single a a 1) (w0 ε m) = (((m a : ℝ)) : ℂ) • w0 ε m := by
  apply MV.ext
  funext x
  rw [dTau_fn, MV.fn_smul, Pi.smul_apply, smul_eq_mul]
  have h := rdc_f0K_wt ε hm a x
  rw [show (w0 ε m).fn = f0K ε m from rfl, h]
  push_cast
  ring

theorem derived_action_highest_vector (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a b : Fin n) (hab : a < b)
    (he : ε a = ε b) : dTau ε m (Matrix.single a b 1) (w0 ε m) = 0 := by
  apply MV.ext
  funext x
  rw [dTau_fn, MV.fn_zero, Pi.zero_apply]
  exact rdc_f0K_hw ε hm hab he x

theorem dTau_wt (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) :
    dTau ε m (Matrix.single a a 1) (wN ε m) = (((m a : ℝ)) : ℂ) • wN ε m := by
  unfold wN
  rw [map_smul, derived_action_weight_vector ε hm a, smul_comm]

theorem dTau_hw (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a b : Fin n) (hab : a < b)
    (he : ε a = ε b) : dTau ε m (Matrix.single a b 1) (wN ε m) = 0 := by
  unfold wN
  rw [map_smul, derived_action_highest_vector ε hm a b hab he, smul_zero]

theorem gen_wN (ε : Fin n → Bool) (m : Fin n → ℤ) (W : Submodule ℂ (MV ε m))
    (hW : ∀ k : KG ε, ∀ v ∈ W, ((tauM ε m k : unitary (MV ε m →L[ℂ] MV ε m)) : MV ε m →L[ℂ] MV ε m) v ∈ W)
    (hw : wN ε m ∈ W) : W = ⊤ := by
  have hn : ‖w0 ε m‖ ≠ 0 := norm_ne_zero_iff.mpr (highest_weight_vector_ne_zero ε m)
  have hw0 : w0 ε m ∈ W := by
    have h : w0 ε m = ((‖w0 ε m‖ : ℝ) : ℂ) • wN ε m := by
      unfold wN
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_smul]
    rw [h]
    exact W.smul_mem _ hw
  have htr : ∀ k : KG ε, rtr ε k (f0K ε m) ∈ W.map (mvFnL ε m) :=
    fun k => ⟨tauC ε m k (w0 ε m), hW k _ hw0, rfl⟩
  have hle : Vsp ε m ≤ W.map (mvFnL ε m) := by
    rw [Vsp, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact htr k
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.mem
  rw [← mvFnL_injective ε m hyx]
  exact hy

def modelKType (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) : KType ε (fun a => (m a : ℝ)) :=
  kTypeOfGen (MV ε m) (tauM ε m) (continuous_tauM ε m) (dTau ε m) (hasDeriv_dTau ε m) (wN ε m) (norm_wN ε m)
    (dTau_wt ε hm) (dTau_hw ε hm) (gen_wN ε m)

theorem model_exists (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) :
    Nonempty (KType ε (fun a => (m a : ℝ))) := ⟨modelKType ε hm⟩

end ReciprocityTheory.ChartRestriction.DS.HW
