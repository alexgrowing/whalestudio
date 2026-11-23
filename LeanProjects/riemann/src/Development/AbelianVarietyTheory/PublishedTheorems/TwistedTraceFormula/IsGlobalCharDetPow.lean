import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.UnitaryOneOneChambers

open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.FormalDegree.Model
open Formalism.REAL (UJ KG muK Jm)
open Formalism.QuantumDeterminants (IsHCParam IsCRepOn)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsDS UJset)
open GlobalTheory.FlagMeas (IsIsoFlag flagM)
open GlobalTheory.FlagMeas.Model (e2 W2)
open scoped ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.HCChar.Model

theorem isGlobalChar_detPow {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (m : ℤ)
    (h : IsURepOn (UJset ε) (detPow n m)) : IsGlobalChar μ (ujRep h) fun g => (ujMat ε g).det ^ m := by
  have hc : Continuous fun g : UJ ε => (ujMat ε g).det ^ m :=
    continuous_ujMat.matrix_det.zpow₀ m fun g => .inl (det_ujMat_ne_zero g)
  refine ⟨⟨hc.locallyIntegrable, fun _ _ => hc.continuousAt, fun f hf => ?_⟩, fun s _ => ⟨⟨fun x => (Matrix.of x).det ^ m,
    ?_, .of_forall fun _ => rfl⟩, fun x => ?_⟩⟩
  · have hf' := continuous_of_mem_ccSmooth isInducing_matCoord.continuous hf
    have hi : Integrable (fun g => f g * (ujMat ε g).det ^ m) μ :=
      (hf'.mul hc).integrable_of_hasCompactSupport hf.1.mul_right
    have e : repOp (ujRep h) μ f = (∫ g, f g * (ujMat ε g).det ^ m ∂μ) • ContinuousLinearMap.id ℂ ℂ := by
      refine IsRepOp.repOp_eq fun v => ?_
      have : (fun g => f g • ujRep h g v) = fun g => f g * (ujMat ε g).det ^ m * v := by
        funext g
        change f g * detPow n m (ujMat ε g) v = _
        rw [detPow_apply, mul_assoc]
      rw [this]
      exact ⟨hi.mul_const v, by simp [integral_mul_const]⟩
    rw [e]
    exact ⟨isTraceClass_of_finiteDimensional _, by simp [trace_eq_linearMap_trace]⟩
  · refine AnalyticAt.zpow ?_ (det_ujMat_ne_zero s)
    simp only [Matrix.det_apply']
    refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ?_)
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) (σ i))).analyticAt _
  · have h1 : (ujMat ε x⁻¹).det * (ujMat ε x).det = 1 := by rw [← det_mul, ← map_mul, inv_mul_cancel, map_one, det_one]
    simp only [map_mul, det_mul]
    rw [mul_right_comm, h1, one_mul]

theorem dsChar_lamDet (n : ℕ) (s : Bool) (m : ℤ) (θ : Fin n → ℝ)
    (hθ : IsRegSS (ujMat (fun _ : Fin n => s) (torusPt _ θ))) :
    dsChar (fun _ : Fin n => s) (lamDet n m) θ = (ujMat (fun _ : Fin n => s) (torusPt _ θ)).det ^ m := by
  have hd := weylDenom_ne_zero hθ
  have hv : (∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I))) ≠ 0 := by
    rw [← weylDenom_mul]; exact mul_ne_zero hd (Complex.exp_ne_zero _)
  rw [dsChar_eq _ (m := fun a => m + ((Fin.rev a : ℕ) : ℤ)) (fun a => by
    have := a.isLt
    simp only [lamDet, Formalism.QuantumDeterminants.rhoStd, Fin.val_rev]
    push_cast [Nat.cast_sub (show (a : ℕ) + 1 ≤ n by omega)]
    ring)]
  have h1 : halfDim (fun _ : Fin n => s) = 0 := by cases s <;> simp [halfDim]
  have h2 : compactWeyl (fun _ : Fin n => s) = Finset.univ := by
    ext w; simp [compactWeyl, Function.comp_def]
  rw [h1, h2, pow_zero, one_mul, div_eq_iff hv, ujMat_torusPt, det_diagonal]
  have h3 := Matrix.det_projVandermonde (fun _ : Fin n => (1 : ℂ)) fun a => Complex.exp (θ a * Complex.I)
  simp only [one_mul] at h3
  rw [← h3, ← det_transpose, det_apply', Finset.mul_sum, ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [zpow_add₀ (Complex.exp_ne_zero _), Finset.prod_mul_distrib, Finset.prod_zpow, zpow_natCast,
    Equiv.inv_apply, Equiv.Perm.sign_inv, transpose_apply, projVandermonde_apply, one_pow, one_mul]
  rw [mul_left_comm]
  rfl

theorem ds_case (n : ℕ) (s : Bool) (m : ℤ) (μ : Measure (UJ fun _ : Fin n => s)) [μ.IsHaarMeasure] :
    IsHCParam (lamDet n m) ∧ IsDS (fun _ : Fin n => s) (lamDet n m) (detPow n m) ∧
      ∀ h : IsURepOn (UJset fun _ : Fin n => s) (detPow n m), ∃ Θ, IsGlobalChar μ (ujRep h) Θ ∧
        ∀ θ : Fin n → ℝ, IsRegSS (ujMat (fun _ : Fin n => s) (torusPt _ θ)) →
          Θ (torusPt _ θ) = dsChar (fun _ : Fin n => s) (lamDet n m) θ :=
  ⟨lamDet_hc n m, isDS_detPow n s m, fun h => ⟨_, isGlobalChar_detPow _ μ m h,
    fun θ hθ => (dsChar_lamDet n s m θ hθ).symm⟩⟩

theorem weyl_one (e : Bool) (μ : Measure (UJ ![e])) [μ.IsHaarMeasure] (𝒯 : Finset (Subgroup (UJ ![e])))
    (h𝒯 : IsCartanSystem 𝒯) (dt : ∀ T : Subgroup (UJ ![e]), Measure T) (hdt : ∀ T ∈ 𝒯, (dt T).IsHaarMeasure)
    (F : UJ ![e] → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ g, F g ∂μ = ∑ T ∈ 𝒯, (weylOrder T : ℝ≥0∞)⁻¹ *
      ∫⁻ t : T, ‖weylDisc (ujMat ![e] t)‖ₑ * ∫⁻ q, F (q.out⁻¹ * t * q.out) ∂quotMeas T (dt T) μ ∂dt T := by
  have comm : ∀ s t : UJ ![e], s * t = t * s := fun s t => Subtype.ext (Units.ext
    (Matrix.ext fun i j => by fin_cases i; fin_cases j; simp [Matrix.mul_apply, mul_comm]))
  have hc : ∀ s : UJ ![e], cent s = ⊤ := fun s => eq_top_iff.2 fun t _ => mem_cent.2 (comm _ _)
  have ht : ∀ T : Subgroup (UJ ![e]), IsCartanSub T → T = ⊤ := fun T ⟨s, _, hs⟩ => hs.trans (hc s)
  obtain ⟨θ, hθ⟩ := exists_isRegSS_torusPt ![e]
  obtain ⟨T, ⟨hT, -⟩, -⟩ := h𝒯.2 _ ⟨_, hθ, rfl⟩
  have hC := h𝒯.1 T hT
  obtain rfl := ht T hC
  obtain rfl : 𝒯 = {⊤} := Finset.eq_singleton_iff_unique_mem.2 ⟨hT, fun T h => ht T (h𝒯.1 T h)⟩
  have := hdt ⊤ hT
  have := hC.isMulRightInvariant (dt ⊤)
  have : LocallyCompactSpace (⊤ : Subgroup (UJ ![e])) := hC.isClosed.locallyCompactSpace
  have hD : ∀ t : UJ ![e], weylDisc (ujMat ![e] t) = 1 := fun t => by
    have : ujMat ![e] t = diagonal fun a => ujMat ![e] t a a := by
      ext i j; fin_cases i; fin_cases j; simp
    have h0 := det_ujMat_ne_zero t
    rw [this, det_diagonal] at h0
    rw [this, weylDisc_diagonal fun a => Finset.prod_ne_zero_iff.1 h0 a (Finset.mem_univ a)]
    simp
  have hw : weylOrder (⊤ : Subgroup (UJ ![e])) = 1 := Subgroup.relIndex_top_left _
  have h1 : ∀ x t : UJ ![e], x⁻¹ * t * x = t := fun x t => by rw [comm x⁻¹, inv_mul_cancel_right]
  have h2 : ∀ x : UJ ![e], ∫⁻ t : (⊤ : Subgroup (UJ ![e])), F (t * x) ∂dt ⊤ =
      ∫⁻ t : (⊤ : Subgroup (UJ ![e])), F t ∂dt ⊤ := fun x =>
    lintegral_mul_right_eq_self (fun t : (⊤ : Subgroup (UJ ![e])) => F t) ⟨x, trivial⟩
  rw [Finset.sum_singleton, isQuotMeasure_quotMeas (dt ⊤) μ hC.isClosed F hF]
  simp only [hD, hw, h1, h2, lintegral_const, Nat.cast_one, inv_one, one_mul, enorm_one]
  rw [lintegral_mul_const (f := fun t : (⊤ : Subgroup (UJ ![e])) => F t) _ (hF.comp measurable_subtype_coe)]

theorem torusPt_not_conj {θ : Fin 2 → ℝ} (h : IsRegSS (ujMat e2 (torusPt e2 θ))) (x : UJ e2) :
    x * torusPt e2 θ * x⁻¹ ∉ flagM e2 W2 := by
  intro hx
  rw [IsRegSS, ujMat_torusPt, charpoly_diagonal, separable_prod_X_sub_C_iff] at h
  have hne : Complex.exp (θ 0 * Complex.I) ≠ Complex.exp (θ 1 * Complex.I) := fun e => by simpa using h e
  have hv : (![1, 1] : Fin 2 → ℂ) ∈ W2 1 := Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hx 1 _ hv).1
  change _ = ujMat e2 (x * torusPt e2 θ * x⁻¹) *ᵥ _ at hc
  set y := ujMat e2 x⁻¹ *ᵥ ![1, 1] with hy
  have e1 : c • y = ujMat e2 (torusPt e2 θ) *ᵥ y := by
    rw [hy, ← mulVec_smul, hc, mulVec_mulVec, mulVec_mulVec, ← map_mul, ← map_mul]
    congr 2
    group
  have hJ : (ujMat e2 x⁻¹)ᴴ * Jm e2 * ujMat e2 x⁻¹ = Jm e2 := (x⁻¹).2
  have e2' : star y ⬝ᵥ (Jm e2 *ᵥ y) = 0 := by
    rw [hy, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hJ]
    simp [Jm, e2, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.diagonal]
  have e3 : ujMat e2 x *ᵥ y = ![1, 1] := by rw [hy, mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec]
  have c0 := congrFun e1 0
  have c1 := congrFun e1 1
  simp only [ujMat_torusPt, mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at c0 c1
  simp [Jm, e2, dotProduct, mulVec_diagonal, Fin.sum_univ_two] at e2'
  have hy0 : y = 0 := by
    have : y 0 = 0 ∧ y 1 = 0 := by
      by_cases h0 : y 0 = 0
      · refine ⟨h0, ?_⟩
        simpa [h0] using e2'
      · have h1 : y 1 = 0 := by
          by_contra h1
          exact hne ((mul_right_cancel₀ h0 c0).symm.trans (mul_right_cancel₀ h1 c1))
        refine ⟨?_, h1⟩
        simpa [h1] using e2'
    funext i; fin_cases i
    exacts [this.1, this.2]
  simpa [hy0] using congrFun e3 0

theorem induced_case (h : GlobalTheory.Published.InducedCharacterSupport) (μ : Measure (UJ e2)) [μ.IsHaarMeasure] :
    ∃ I : GlobalTheory.RealInd.IndModule e2, (∃ w : I.H, ‖w‖ = 1) ∧ ∃ Θ, IsGlobalChar μ I.rep Θ ∧
      (∃ θ, IsRegSS (ujMat e2 (torusPt e2 θ))) ∧ ∀ θ, IsRegSS (ujMat e2 (torusPt e2 θ)) → Θ (torusPt e2 θ) = 0 := by
  obtain ⟨I, hI, -, -, w, hw, -⟩ := GlobalTheory.RealInd.exists_standard_indModule (s := 1) (by simp)
  obtain ⟨D, H, ρ, ι, hm⟩ := I
  obtain rfl : D = _ := hI
  obtain ⟨Θ, h1, h2⟩ := h.indModule μ ⟨_, H, ρ, ι, hm⟩ one_ne_zero
  exact ⟨_, ⟨w, hw⟩, Θ, h1, exists_isRegSS_torusPt _, fun θ hθ => h2 _ hθ (torusPt_not_conj hθ)⟩

end GlobalTheory.HCChar.Model
