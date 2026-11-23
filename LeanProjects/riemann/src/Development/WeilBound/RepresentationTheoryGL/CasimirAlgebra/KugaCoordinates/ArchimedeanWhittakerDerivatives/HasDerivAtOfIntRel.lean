import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ContinuousInfGL
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.AvgIntegralSwap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousUnipotentColumnWhittakerTransform

noncomputable section

namespace PositivityTheory.Rg.Cz

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def IntRel (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0) (f f' : GA E a → ℂ) : Prop :=
  ∀ g t, f (g * infGL E a (cu M hM t)) - f g = ∫ s in (0 : ℝ)..t, f' (g * infGL E a (cu M hM s))

theorem intRel_sm (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0) (φ : Sm E a) :
    IntRel M hM φ.1 (lieD (toL M) φ.1) := by
  intro g t
  have hd : ∀ s, HasDerivAt (fun u => φ.1 (g * infGL E a (cu M hM u)))
      (lieD (toL M) φ.1 (g * infGL E a (cu M hM s))) s := by
    intro s
    have h1 := hasDerivAt_curve φ (g * infGL E a (cu M hM s)) (cu M hM) (toL M) (cu_zero M hM) (hasDerivAt_cu M hM 0)
    have h1' : HasDerivAt (fun u => φ.1 (g * infGL E a (cu M hM s) * infGL E a (cu M hM u)))
        (lieD (toL M) φ.1 (g * infGL E a (cu M hM s))) (s - s) := by rwa [sub_self]
    have h2 := HasDerivAt.scomp (h := fun u : ℝ => u - s) s h1' ((hasDerivAt_id' s).sub_const s)
    rw [one_smul] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp_apply]
    rw [mul_assoc, ← map_mul, ← cu_add, add_sub_cancel]
  have hcont : Continuous fun s => lieD (toL M) φ.1 (g * infGL E a (cu M hM s)) := by
    have hm := lieD_mem_Sm (toL M) φ.2
    have hc : Continuous fun s => toL (cu M hM s).val :=
      continuous_iff_continuousAt.2 fun s => (hasDerivAt_cu M hM s).continuousAt
    have h3 := ((hm g).continuousOn).comp_continuous hc (fun s => val_mem_invSet _)
    simpa only [Function.comp_def, chart_val] using h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hcont.intervalIntegrable _ _)]
  simp only [cu_zero, map_one, mul_one]

theorem intRel_colT {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0)
    {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ (m + 1) f) (hf' : Good ψ (m + 1) f') (h : IntRel M hM f f') :
    IntRel M hM (colT ψ (m + 1) f) (colT ψ (m + 1) f') := by
  intro g t
  have hΓ := isCoLat_ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))
  have hl := hl_of_good hf le_rfl
  have hl' := hl_of_good hf' le_rfl
  set ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E := eLast a (m + 1)
  have e0 : colT ψ (m + 1) f (g * infGL E a (cu M hM t)) - colT ψ (m + 1) f g =
      avg (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => ψ (-dot ξ x) * f (blkU x * (g * infGL E a (cu M hM t))) -
        ψ (-dot ξ x) * f (blkU x * g)) :=
    (avg_sub _ hΓ _ _ (per_coef hψ ξ hf.cont hl _) (per_coef hψ ξ hf.cont hl _)).symm
  have e1 : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => ψ (-dot ξ x) * f (blkU x * (g * infGL E a (cu M hM t))) -
        ψ (-dot ξ x) * f (blkU x * g)) =
      fun x => ∫ s in (0 : ℝ)..t, ψ (-dot ξ x) * f' (blkU x * (g * infGL E a (cu M hM s))) := by
    funext x
    have h2 := h (blkU x * g) t
    simp only [mul_assoc] at h2
    rw [← mul_sub, h2, intervalIntegral.integral_const_mul]
  have hF : Continuous fun p : (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) × ℝ =>
      ψ (-dot ξ p.1) * f' (blkU p.1 * (g * infGL E a (cu M hM p.2))) := by
    have hb : Continuous fun p : (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) × ℝ => (blkU p.1 : GA E a) :=
      (continuous_posU (isNil_blk a (m + 1) (m + 1))).comp continuous_fst
    have hc : Continuous fun p : (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) × ℝ => infGL E a (cu M hM p.2) :=
      (continuous_infGL' E a).comp ((continuous_cu M hM).comp continuous_snd)
    exact (hψ.cont.comp ((continuous_dot ξ).neg.comp continuous_fst)).mul
      (hf'.cont.comp (hb.mul (continuous_const.mul hc)))
  have hp : ∀ γ ∈ ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)), ∀ x s,
      (fun p : (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) × ℝ => ψ (-dot ξ p.1) * f' (blkU p.1 * (g * infGL E a (cu M hM p.2))))
        (γ + x, s) =
      (fun p : (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) × ℝ => ψ (-dot ξ p.1) * f' (blkU p.1 * (g * infGL E a (cu M hM p.2))))
        (x, s) :=
    fun γ hγ x s => (per_coef hψ ξ hf'.cont hl' (g * infGL E a (cu M hM s))).2 γ hγ x
  rw [e0, e1]
  exact avg_integral_swap _ hΓ _ hF hp t

theorem intRel_whit {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0)
    (m : ℕ) : (m < a ∨ m = 0) → ∀ {f f' : GA E a → ℂ}, Good ψ m f → Good ψ m f' → IntRel M hM f f' →
      IntRel M hM (whit ψ m f) (whit ψ m f') := by
  induction m with
  | zero => exact fun _ _ _ _ _ h => h
  | succ m ih =>
    intro hm f f' hf hf' h
    have h1 : m + 1 < a := by omega
    exact ih (Or.inl (by omega)) (good_colT hψ h1 hf) (good_colT hψ h1 hf') (intRel_colT hψ M hM hf hf' h)

theorem hasDerivAt_of_intRel (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0) {F F' : GA E a → ℂ}
    (hc : Continuous F') (h : IntRel M hM F F') (g : GA E a) :
    HasDerivAt (fun t => F (g * infGL E a (cu M hM t))) (F' g) 0 := by
  have hcont : Continuous fun s : ℝ => F' (g * infGL E a (cu M hM s)) :=
    hc.comp (continuous_const.mul ((continuous_infGL' E a).comp (continuous_cu M hM)))
  have e : (fun t => F (g * infGL E a (cu M hM t))) =
      fun t => F g + ∫ s in (0 : ℝ)..t, F' (g * infGL E a (cu M hM s)) := by
    funext t; rw [← h g t]; ring
  rw [e]
  have h1 := (hcont.integral_hasStrictDerivAt 0 0).hasDerivAt
  simp only [cu_zero, map_one, mul_one] at h1
  exact h1.const_add (F g)

end PositivityTheory.Rg.Cz
