import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormSliceRLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivPdLe

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOpDeriv

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem pd_padL_add (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (h h' : κ → V) :
    pd (padL (κ' := κ') (h + h')) f = pd (padL h) f + pd (padL h') f := by
  have e : (padL (κ' := κ') (h + h') : κ ⊕ κ' → V) = padL h + padL h' := by
    funext i; cases i <;> simp [padL]
  ext z
  rw [SchwartzMap.add_apply, pd_apply, pd_apply, pd_apply, e, map_add]

theorem pd_padL_smul (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (c : ℝ) (h : κ → V) :
    pd (padL (κ' := κ') (c • h)) f = (c : ℂ) • pd (padL h) f := by
  have e : (padL (κ' := κ') (c • h) : κ ⊕ κ' → V) = c • padL h := by
    funext i; cases i <;> simp [padL]
  ext z
  rw [SchwartzMap.smul_apply, pd_apply, pd_apply, e, map_smul, Complex.real_smul, smul_eq_mul]

def xPartL (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : (κ → V) →ₗ[ℝ] ℂ where
  toFun h := P (sliceR (pd (padL (κ' := κ') h) f) x) y
  map_add' h h' := by
    simp only [pd_padL_add, ← sliceRL_apply, map_add, SchwartzMap.add_apply]
  map_smul' c h := by
    simp only [pd_padL_smul, ← sliceRL_apply, map_smul, SchwartzMap.smul_apply, RingHom.id_apply,
      Complex.real_smul, smul_eq_mul]

variable [FiniteDimensional ℝ V]

def xPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : (κ → V) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (xPartL P f x y)

theorem xPart_apply (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) (h : κ → V) :
    xPart P f x y h = P (sliceR (pd (padL (κ' := κ') h) f) x) y := rfl

end GlobalTheory.SliceOpDeriv

namespace GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem hasFDerivAt_sliceR_apply (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) :
    HasFDerivAt (fun x' => P (sliceR f x') y) (xPart P f x y) x := by
  obtain ⟨s', C, hC, hP⟩ := clm_sup_bound P {((0 : ℕ), (0 : ℕ))}
  set M : ℝ := s'.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 (m.2 + 2)) f
  have hM : 0 ≤ M := by positivity
  have hb : ∀ h : κ → V, ‖P (sliceR f (x + h)) y - P (sliceR f x) y - xPart P f x y h‖ ≤ C * M * ‖h‖ ^ 2 := by
    intro h
    set D := sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x
    have e : P (sliceR f (x + h)) y - P (sliceR f x) y - xPart P f x y h = P D y := by
      simp only [D, xPart_apply, map_sub, SchwartzMap.sub_apply]
    rw [e]
    have h1 : ‖P D y‖ ≤ ({((0 : ℕ), (0 : ℕ))} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (κ₁' → V) ℂ) (P D) := by
      simpa [schwartzSeminormFamily] using SchwartzMap.norm_le_seminorm ℂ (P D) y
    have h2 : s'.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) D ≤ ‖h‖ ^ 2 * M := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      refine (GlobalTheory.SliceTaylor.seminorm_slice_taylor_le V κ κ' f i.1 i.2 x h).trans ?_
      gcongr
      exact Seminorm.le_finset_sup_apply (p := fun m : ℕ × ℕ => (SchwartzMap.seminorm ℂ m.1 (m.2 + 2) : Seminorm ℂ (SchwartzMap (κ ⊕ κ' → V) ℂ))) (x := f) hi
    calc ‖P D y‖ ≤ C * s'.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) D := h1.trans (hP D)
      _ ≤ C * (‖h‖ ^ 2 * M) := mul_le_mul_of_nonneg_left h2 hC
      _ = C * M * ‖h‖ ^ 2 := by ring
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C * M) (Filter.Eventually.of_forall fun h => ?_)
  refine (hb h).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

end GlobalTheory.SliceOpDeriv

namespace GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem continuous_elim_pair :
    Continuous (fun p : (κ → V) × (κ₁' → V) => (Sum.elim p.1 p.2 : κ ⊕ κ₁' → V)) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl i => simp only [Sum.elim_inl]; fun_prop
  | inr j => simp only [Sum.elim_inr]; fun_prop

theorem qOp_elim (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : qOp P f (Sum.elim x y) = P (sliceR f x) y := by
  simp [qOp]

theorem continuous_xPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun p : (κ → V) × (κ₁' → V) => xPart P f p.1 p.2) := by
  refine continuous_clm_apply.2 fun h => ?_
  have e : (fun p : (κ → V) × (κ₁' → V) => xPart P f p.1 p.2 h) =
      fun p => qOp P (pd (padL (κ' := κ') h) f) (Sum.elim p.1 p.2) := by
    funext p; rw [qOp_elim, xPart_apply]
  rw [e]
  exact (continuous_qOp V κ κ' κ₁' P _).comp continuous_elim_pair

theorem continuous_yPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun p : (κ → V) × (κ₁' → V) => fderiv ℝ (P (sliceR f p.1)) p.2) := by
  refine continuous_clm_apply.2 fun w => ?_
  have e : (fun p : (κ → V) × (κ₁' → V) => fderiv ℝ (P (sliceR f p.1)) p.2 w) =
      fun p => qOp ((pd w).comp P) f (Sum.elim p.1 p.2) := by
    funext p; rw [qOp_elim, ContinuousLinearMap.comp_apply, pd_apply]
  rw [e]
  exact (continuous_qOp V κ κ' κ₁' _ _).comp continuous_elim_pair

def splitL : (κ ⊕ κ₁' → V) →L[ℝ] (κ → V) × (κ₁' → V) :=
  (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ₁' => V) (Sum.inl i)).prod
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ₁' => V) (Sum.inr j))

theorem hasFDerivAt_qOp (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V) :
    HasFDerivAt (qOp P f)
      (((xPart P f (s ∘ Sum.inl) (s ∘ Sum.inr)).coprod
        (fderiv ℝ (P (sliceR f (s ∘ Sum.inl))) (s ∘ Sum.inr))).comp splitL) s := by
  let F : (κ → V) → (κ₁' → V) → ℂ := fun x y => P (sliceR f x) y
  have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := splitL s) (f := F)
    (f₁ := fun x y => xPart P f x y) (f₂ := fun x y => fderiv ℝ (P (sliceR f x)) y)
    (Filter.Eventually.of_forall fun v => hasFDerivAt_sliceR_apply P f v.1 v.2)
    (Filter.Eventually.of_forall fun v => ((P (sliceR f v.1)).differentiableAt).hasFDerivAt)
    (continuous_xPart P f).continuousAt (continuous_yPart P f).continuousAt
  have h2 := key.hasFDerivAt.comp s ((splitL (V := V) (κ := κ) (κ₁' := κ₁')).hasFDerivAt (x := s))
  exact h2

end GlobalTheory.SliceOpDeriv

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp in
theorem GlobalTheory.SliceOp.differentiable_qOp_and_fderiv : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ),
    Differentiable ℝ (qOp P f) ∧ ∀ (s v : κ ⊕ κ₁' → V),
      fderiv ℝ (qOp P f) s v = qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s := by
  intro V _ _ _ κ κ' κ₁' _ _ _ P f
  refine ⟨fun s => (GlobalTheory.SliceOpDeriv.hasFDerivAt_qOp P f s).differentiableAt, fun s v => ?_⟩
  rw [(GlobalTheory.SliceOpDeriv.hasFDerivAt_qOp P f s).fderiv]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply]
  rfl
