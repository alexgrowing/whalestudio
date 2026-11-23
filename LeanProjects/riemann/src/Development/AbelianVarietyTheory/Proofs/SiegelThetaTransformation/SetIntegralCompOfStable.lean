import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LowestWeightFunctionMulEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianKernelIntegrableOnThinSlabStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPlaceKernelHolomorphicWeightRowHighestStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Repro

theorem setIntegral_comp_of_stable {V : Type} [MeasurableSpace V] {ν : Measure V} {S : Set V}
    (hS : MeasurableSet S) {u : V → V} (hu : MeasurePreserving u ν ν) (hSu : ∀ x, u x ∈ S ↔ x ∈ S)
    {f : V → ℂ} (hf : AEStronglyMeasurable f (ν.restrict S)) :
    ∫ x in S, f (u x) ∂ν = ∫ x in S, f x ∂ν := by
  have h := hu.restrict_preimage hS
  rw [show u ⁻¹' S = S from Set.ext hSu] at h
  rw [← integral_map h.measurable.aemeasurable (by rwa [h.map_eq]), h.map_eq]

theorem exists_mean {K V : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [SecondCountableTopology K]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (ν : Measure V) [SFinite ν] {U S : Set V} (hU : IsOpen U) (hS : IsOpen S)
    (hSU : S ⊆ U) (A : K → V → V) (hA : Continuous (Function.uncurry A))
    (hAd : ∀ t, Differentiable ℂ (A t)) (hmul : ∀ s t x, A (t * s) x = A t (A s x))
    (hAU : ∀ t x, x ∈ U → A t x ∈ U) (hAS : ∀ t x, A t x ∈ S ↔ x ∈ S)
    (hν : ∀ t, MeasurePreserving (A t) ν ν) (χ : K → ℂ) (hχ : Continuous χ)
    (hχ1 : ∀ t, ‖χ t‖ = 1) (hχm : ∀ s t, χ (t * s) = χ t * χ s)
    (k F : V → ℂ) (hk : IntegrableOn k S ν) (hkA : ∀ t, ∀ x ∈ S, k (A t x) * χ t = k x)
    (hF : DifferentiableOn ℂ F U) (C : ℝ) (hC : ∀ x ∈ S, ‖F x‖ ≤ C) :
    ∃ G : V → ℂ, DifferentiableOn ℂ G U ∧ (∀ s x, G (A s x) = χ s * G x) ∧
      (∀ x y c, (∀ t, F (A t y) = c * F (A t x)) → G y = c * G x) ∧
      (∀ x, (∀ t, F (A t x) = χ t * F x) → G x = F x) ∧
      ∫ x in S, k x * G x ∂ν = ∫ x in S, k x * F x ∂ν := by
  borelize K
  have : SecondCountableTopology V := by
    have : ProperSpace V := FiniteDimensional.proper ℂ V
    infer_instance
  let μ : Measure K := (Measure.haarMeasure ⊤).inv
  have hp : IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) :=
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))⟩
  have hp' : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  have hχ0 : ∀ t, χ t ≠ 0 := fun t h => by simpa [h] using hχ1 t
  have hcont : ContinuousOn (Function.uncurry fun t x => (χ t)⁻¹ * F (A t x)) (Set.univ ×ˢ U) := by
    refine ContinuousOn.mul ?_ ?_
    · exact ((hχ.inv₀ hχ0).comp continuous_fst).continuousOn
    · exact hF.continuousOn.comp hA.continuousOn fun p hp => hAU _ _ hp.2
  refine ⟨fun x => ∫ t, (χ t)⁻¹ * F (A t x) ∂μ, ?_, fun s x => ?_, fun x y c h => ?_,
    fun x h => ?_, ?_⟩
  · exact (differentiableOn_integral_of_holomorphic_of_continuousOn (μ := μ) hU hcont fun t =>
      (hF.comp (hAd t).differentiableOn fun x hx => hAU t x hx).const_mul _).1
  · have h := integral_mul_right_eq_self (μ := μ) (fun t => (χ t)⁻¹ * F (A t x)) s
    simp only
    rw [← h, ← integral_const_mul]
    congr 1
    funext t
    rw [hmul, hχm]
    have := hχ0 s
    field_simp
  · simp only
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [h]; ring
  · simp only [h, ← mul_assoc, inv_mul_cancel₀ (hχ0 _), one_mul]
    simp
  · have hint : Integrable (Function.uncurry fun x t => k x * ((χ t)⁻¹ * F (A t x)))
        ((ν.restrict S).prod μ) := by
      have h1 : Integrable (fun p : V × K => k p.1) ((ν.restrict S).prod μ) := hk.comp_fst μ
      have e : (ν.restrict S).prod μ = (ν.prod μ).restrict (S ×ˢ Set.univ) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      have hm : MeasurableSet (S ×ˢ (Set.univ : Set K)) := hS.measurableSet.prod MeasurableSet.univ
      suffices h3 : Integrable (fun p : V × K => k p.1 * ((χ p.2)⁻¹ * F (A p.2 p.1)))
        ((ν.restrict S).prod μ) from h3
      refine h1.mul_bdd (c := C) ?_ ?_
      · rw [e]
        refine ContinuousOn.aestronglyMeasurable ?_ hm
        refine ContinuousOn.mul ?_ ?_
        · exact ((hχ.inv₀ hχ0).comp continuous_snd).continuousOn
        · exact hF.continuousOn.comp (f := fun p : V × K => A p.2 p.1)
            (hA.comp continuous_swap).continuousOn fun p hp => hAU _ _ (hSU hp.1)
      · rw [e]
        refine ae_restrict_of_forall_mem hm fun p hp => ?_
        rw [norm_mul, norm_inv, hχ1, inv_one, one_mul]
        exact hC _ ((hAS _ _).2 hp.1)
    have hkF : AEStronglyMeasurable (fun x => k x * F x) (ν.restrict S) :=
      hk.aestronglyMeasurable.mul
        ((hF.continuousOn.mono hSU).aestronglyMeasurable hS.measurableSet)
    simp only [← integral_const_mul]
    rw [integral_integral_swap hint]
    have h2 : ∀ t, ∫ x in S, k x * ((χ t)⁻¹ * F (A t x)) ∂ν = ∫ x in S, k x * F x ∂ν := by
      intro t
      rw [← setIntegral_comp_of_stable hS.measurableSet (hν t) (hAS t) hkF]
      refine setIntegral_congr_fun hS.measurableSet fun x hx => ?_
      beta_reduce
      rw [← hkA t x hx]
      have := hχ0 t
      field_simp
    simp [h2]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem unitary_of_gram_eq (τ : E →+* ℂ) {x y : Matrix (Fin r) (Fin r) ℂ} (hx : x.det ≠ 0)
    (h : gram τ X.Gm y = gram τ X.Gm x) (v w : Fin r → ℂ) :
    hermC τ X.Gm ((y * x⁻¹) *ᵥ v) ((y * x⁻¹) *ᵥ w) = hermC τ X.Gm v w := by
  have h1 : gram τ X.Gm (y * x⁻¹) = gram τ X.Gm 1 := by
    rw [FrameDegreeData.gram_mul, h, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hx)]
  have h2 : ∀ u : Matrix (Fin r) (Fin r) ℂ, hermC τ X.Gm (u *ᵥ v) (u *ᵥ w) =
      v ⬝ᵥ gram τ X.Gm u *ᵥ star w := by
    intro u
    rw [FrameDegreeData.gram_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [h2, h1, ← h2, Matrix.one_mulVec, Matrix.one_mulVec]

theorem differentiable_lmulC (u : X.Ψ → Matrix (Fin r) (Fin r) ℂ) :
    Differentiable ℂ (X.lmulC u) := by
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  simp only [Data.lmulC, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem lmulC_rmul (u : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x b : Frame X.Ψ r) :
    X.lmulC u (rmul x b) = rmul (X.lmulC u x) b := by
  funext τ
  exact (Matrix.mul_assoc (u τ) (mat x τ) (mat b τ)).symm

theorem lmulC_div (x y : Frame X.Ψ r) (hx : x ∈ X.dom) :
    X.lmulC (fun τ => mat y τ * (mat x τ)⁻¹) x = y := by
  funext τ
  exact Matrix.nonsing_inv_mul_cancel_right _ _ (isUnit_iff_ne_zero.2 (hx τ).1)

theorem exists_bchar_bound (la : Wt X.Ψ r) (C : ℝ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ b : Frame X.Ψ r,
    (∀ τ i j, ‖b τ i j‖ ≤ C ∧ ‖(b τ i i)⁻¹‖ ≤ C) → ‖bchar la b‖ ≤ D := by
  refine ⟨∏ τ, ∏ i, |C| ^ (la τ i).natAbs, by positivity, fun b hb => ?_⟩
  rw [bchar, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  obtain ⟨n, h | h⟩ := Int.eq_nat_or_neg (la τ i)
  · rw [h, zpow_natCast, norm_pow, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hb τ i i).1.trans (le_abs_self C)) n
  · rw [h, _root_.zpow_neg, zpow_natCast, ← inv_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hb τ i i).2.trans (le_abs_self C)) n

theorem pnorm_ortho (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X) : X.pnorm la F x = ‖F x‖ := by
  have h2 : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1 := fun τ i => by
    rw [dmin, hx τ, Slab.lminor_sgnM]
    rcases Slab.psgn_sq X.p0 i with h | h <;> simp [h]
  simp [Data.pnorm, h2]

theorem isAddHaarMeasure_volume : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure := by
  have _ : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem integral_mul_ortho (la : Wt X.Ψ r) {x₀ : Frame X.Ψ r}
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X) (hx₀' : x₀ ∈ X.dom)
    {S : Set (Frame X.Ψ r)} (hS : IsOpen S) (hSU : S ⊆ X.dom)
    (hu : ∀ u, X.IsUnitaryC u → MeasurePreserving (X.lmulC u) volume volume ∧
      (∀ x, X.lmulC u x ∈ S ↔ x ∈ S) ∧ ∀ x, X.lmulC u x ∈ X.dom ↔ x ∈ X.dom)
    (κ : Frame X.Ψ r → Frame X.Ψ r → ℂ)
    (hinv : ∀ u, X.IsUnitaryC u → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom,
      κ (X.lmulC u x₁) (X.lmulC u x₂) = κ x₁ x₂)
    (hsym : ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, κ x₂ x₁ = conj (κ x₁ x₂))
    (hhol : ∀ x₂ ∈ X.dom, DifferentiableOn ℂ (fun x₁ => κ x₁ x₂) X.dom ∧
      ∀ x₁ ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x₁ b) x₂ = bchar la b * κ x₁ x₂)
    (hint : IntegrableOn (κ x₀) S volume) (F : Frame X.Ψ r → ℂ)
    (hF : DifferentiableOn ℂ F X.dom)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, F (rmul x b) = bchar la b * F x)
    (C : ℝ) (hC : ∀ x ∈ S, ‖F x‖ ≤ C) :
    (∫ x in S, κ x₀ x * F x) * κ x₀ x₀ = (∫ x in S, κ x₀ x * κ x x₀) * F x₀ := by
  have _ := isAddHaarMeasure_volume X
  let T : (X.Ψ → Fin r → ℂ) → X.Ψ → Matrix (Fin r) (Fin r) ℂ :=
    fun t τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹
  have hdet : ∀ τ, IsUnit (mat x₀ τ).det := fun τ => isUnit_iff_ne_zero.2 (hx₀' τ).1
  have hTu : ∀ t, (∀ τ i, ‖t τ i‖ = 1) → X.IsUnitaryC (T t) := by
    intro t ht τ v w
    refine unitary_of_gram_eq X τ.1 (hx₀' τ).1 ?_ v w
    rw [FrameDegreeData.gram_mul, hx₀ τ, sgnM, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    have h := Complex.mul_conj' (t τ a)
    rw [ht, Complex.ofReal_one] at h
    linear_combination ((sgn X.p0 a : ℝ) : ℂ) * h
  have hT0 : ∀ t, X.lmulC (T t) x₀ = rmul x₀ fun τ => Matrix.diagonal (t τ) := fun t =>
    lmulC_div X x₀ (rmul x₀ fun τ => Matrix.diagonal (t τ)) hx₀'
  have hbor : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) →
      (fun τ => Matrix.diagonal (t τ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
    intro t ht τ
    refine ⟨?_, fun a c h => Matrix.diagonal_apply_ne _ h.ne'⟩
    change (Matrix.diagonal (t τ)).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ h => by simpa [h] using ht τ i
  have hchar : ∀ t : X.Ψ → Fin r → ℂ, bchar la (fun τ => Matrix.diagonal (t τ) : Frame X.Ψ r) =
      ∏ τ, ∏ i, t τ i ^ la τ i := fun t => by simp [bchar]
  have hnorm : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ‖∏ τ, ∏ i, t τ i ^ la τ i‖ = 1 :=
    fun t ht => by simp [norm_prod, ht]
  have hk : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      κ x₀ (X.lmulC (T t) x) * ∏ τ, ∏ i, t τ i ^ la τ i = κ x₀ x := by
    intro t ht x hx
    rw [← hinv _ (hTu t ht) x₀ hx₀' x hx, hT0,
      (hhol _ (((hu _ (hTu t ht)).2.2 x).2 hx)).2 x₀ hx₀' _ (hbor t ht), hchar, mul_comm]
  have hc1 : ∀ (t : X.Ψ → Fin r → Circle) τ i, ‖(t τ i : ℂ)‖ = 1 := fun t τ i => Circle.norm_coe _
  have a1 : Continuous (Function.uncurry fun t : X.Ψ → Fin r → Circle =>
      X.lmulC (T fun τ i => t τ i)) := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Function.uncurry, Data.lmulC, T, Matrix.mul_apply (N := (mat x₀ τ)⁻¹),
      Matrix.mul_apply (N := mat _ τ), Matrix.mul_diagonal]
    simp only [mat, Matrix.of_apply]
    fun_prop
  have a2 : ∀ (s t : X.Ψ → Fin r → Circle) x, X.lmulC (T fun τ i => (t * s) τ i) x =
      X.lmulC (T fun τ i => t τ i) (X.lmulC (T fun τ i => s τ i) x) := by
    intro s t x
    funext τ
    change (mat x₀ τ * Matrix.diagonal (fun i => ((t τ i * s τ i : Circle) : ℂ)) * (mat x₀ τ)⁻¹ *
      mat x τ : Matrix (Fin r) (Fin r) ℂ) =
      mat x₀ τ * Matrix.diagonal (fun i => (t τ i : ℂ)) * (mat x₀ τ)⁻¹ *
        (mat x₀ τ * Matrix.diagonal (fun i => (s τ i : ℂ)) * (mat x₀ τ)⁻¹ * mat x τ)
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hdet τ), Circle.coe_mul,
      ← Matrix.diagonal_mul_diagonal]
  have a3 : Continuous fun t : X.Ψ → Fin r → Circle => ∏ τ, ∏ i, (t τ i : ℂ) ^ la τ i := by
    refine continuous_finset_prod _ fun τ _ => continuous_finset_prod _ fun i _ => ?_
    exact Continuous.zpow₀ (by fun_prop) _ fun t => Or.inl (Circle.coe_ne_zero _)
  have a4 : ∀ s t : X.Ψ → Fin r → Circle, ∏ τ, ∏ i, ((t * s) τ i : ℂ) ^ la τ i =
      (∏ τ, ∏ i, (t τ i : ℂ) ^ la τ i) * ∏ τ, ∏ i, (s τ i : ℂ) ^ la τ i := by
    intro s t
    simp only [Pi.mul_apply, Circle.coe_mul, mul_zpow, Finset.prod_mul_distrib]
  obtain ⟨G, hG, hGT, hGB, hG0, hGI⟩ := exists_mean (K := X.Ψ → Fin r → Circle) volume
    (FourierCoefficientDomain.isOpen_dom X) hS hSU (fun t => X.lmulC (T fun τ i => t τ i)) a1
    (fun t => differentiable_lmulC X _) a2 (fun t x hx => ((hu _ (hTu _ (hc1 t))).2.2 x).2 hx)
    (fun t => (hu _ (hTu _ (hc1 t))).2.1) (fun t => (hu _ (hTu _ (hc1 t))).1)
    (fun t => ∏ τ, ∏ i, (t τ i : ℂ) ^ la τ i) a3 (fun t => hnorm _ (hc1 t)) a4 (κ x₀) F hint
    (fun t x hx => hk _ (hc1 t) x (hSU hx)) hF C hC
  have hG0' : G x₀ = F x₀ := hG0 x₀ fun t => by
    rw [hT0, hB x₀ hx₀' _ (hbor _ (hc1 t)), hchar]
  have key := lowest_weight_function_mul_eq X la x₀ hx₀ hx₀' G (fun x => κ x x₀) hG
    (hhol x₀ hx₀').1 (fun x hx b hb => hGB _ _ _ fun t => by
      rw [lmulC_rmul, hB _ (((hu _ (hTu _ (hc1 t))).2.2 x).2 hx) b hb])
    (hhol x₀ hx₀').2
    (fun t ht x hx => hGT (fun τ i => ⟨t τ i, mem_sphere_zero_iff_norm.2 (ht τ i)⟩) x)
    (fun t ht x hx => by
      have h := congrArg conj (hk t ht x hx)
      rw [map_mul, ← hsym x₀ hx₀' x hx,
        ← hsym x₀ hx₀' _ (((hu _ (hTu t ht)).2.2 x).2 hx)] at h
      have h1 := Complex.mul_conj' (∏ τ, ∏ i, t τ i ^ la τ i)
      rw [hnorm t ht, Complex.ofReal_one] at h1
      rw [← h]
      change κ (X.lmulC (T t) x) x₀ = _
      linear_combination (-κ (X.lmulC (T t) x) x₀) * h1)
  rw [← hGI, ← integral_mul_const, ← integral_mul_const]
  refine setIntegral_congr_fun hS.measurableSet fun x hx => ?_
  beta_reduce
  rw [mul_assoc, key x (hSU hx), hG0', mul_assoc]

end GlobalTheory.SW.Repro

namespace GlobalTheory.SW

open Repro in

theorem kern_reproducing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → 2 * r ≤ n → (∃ j, P j ≠ 0) → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∃ a : ℝ, 0 < a ∧ ∀ F : Frame X.Ψ r → ℂ, DifferentiableOn ℂ F X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, F (rmul x b) = bchar (wtOf X hr c c' n) b * F x) → (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (wtOf X hr c c' n) F x ≤ C) → ∀ x₁ ∈ X.dom, ∫ x₂ in slab X δ, kern X hr idx P x₁ x₂ * F x₂ = a * F x₁ := by
  intro E _ _ _ r X g q0 hr idx n c c' m P hn hP hrn hP0
  have _ := isAddHaarMeasure_volume X
  obtain ⟨δ₀, hδ₀, h₀⟩ := thin_slab E r X
  obtain ⟨δ₁, hδ₁, h₁⟩ := GlobalTheory.T.gaussianKernel_integrableOn_thin_slab E r X g q0 hr idx n c c' m P hn hP hrn
  obtain ⟨hinv, hsym, hpos⟩ := kern_invariant_symm_pos E r X g q0 hr idx n c c' m P hn hP
  have hhol := GlobalTheory.T.realPlaceKernel_holomorphic_weight_rowHighest E r X g q0 hr idx n c c' m P hn hP
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun δ hδ hle => ?_⟩
  obtain ⟨hS, hSU, hort, ⟨x₀, hx₀⟩, hu, ⟨C₀, hC₀⟩, hdec⟩ := h₀ δ hδ (hle.trans (min_le_left _ _))
  have hx₀' : x₀ ∈ X.dom := hSU (hort x₀ hx₀)
  obtain ⟨hint, C₁, hC₁⟩ := h₁ δ hδ (hle.trans (min_le_right _ _)) x₀ hx₀'
  set κ := kern X hr idx P with hκ
  have hcont : ∀ x₁ ∈ X.dom, ContinuousOn (κ x₁) (slab X δ) := fun x₁ hx₁ =>
    (Complex.continuous_conj.comp_continuousOn ((hhol x₁ hx₁).1.continuousOn.mono hSU)).congr
      fun x hx => hsym x (hSU hx) x₁ hx₁
  have hre : κ x₀ x₀ = ((κ x₀ x₀).re : ℂ) :=
    (Complex.conj_eq_iff_re.1 (hsym x₀ hx₀' x₀ hx₀').symm).symm
  have hk0 : 0 < (κ x₀ x₀).re := hpos hP0 x₀ hx₀
  have hI : ∫ x in slab X δ, κ x₀ x * κ x x₀ = ((∫ x in slab X δ, ‖κ x₀ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun hS.measurableSet fun x hx => ?_
    beta_reduce
    rw [hsym x₀ hx₀' x (hSU hx), Complex.mul_conj']
    push_cast
    rfl
  have hIpos : 0 < ∫ x in slab X δ, ‖κ x₀ x‖ ^ 2 := by
    have hi : IntegrableOn (fun x => ‖κ x₀ x‖ ^ 2) (slab X δ) volume := by
      simp only [sq]
      refine Integrable.mul_bdd (c := C₁) hint.norm hint.norm.aestronglyMeasurable ?_
      exact ae_restrict_of_forall_mem hS.measurableSet fun x hx => by
        rw [norm_norm]; exact hC₁ x hx
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hi]
    have ho : IsOpen (slab X δ ∩ κ x₀ ⁻¹' {0}ᶜ) :=
      (hcont x₀ hx₀').isOpen_inter_preimage hS isOpen_compl_singleton
    refine (ho.measure_pos volume ⟨x₀, hort x₀ hx₀, fun h => ?_⟩).trans_le
      (measure_mono fun x hx => ⟨?_, hx.1⟩)
    · rw [Set.mem_singleton_iff.1 h] at hk0
      simp at hk0
    · exact pow_ne_zero 2 (norm_ne_zero_iff.2 hx.2)
  refine ⟨(∫ x in slab X δ, ‖κ x₀ x‖ ^ 2) / (κ x₀ x₀).re, div_pos hIpos hk0,
    fun F hF hB ⟨C, hC⟩ x₁ hx₁ => ?_⟩
  obtain ⟨D, hD0, hD⟩ := exists_bchar_bound X (wtOf X hr c c' n) C₀
  have hFb : ∀ x ∈ slab X δ, ‖F x‖ ≤ D * C := by
    intro x hx
    obtain ⟨x', hx', b, hb, rfl, hbC⟩ := hC₀ x hx
    have h := hC x' (hSU (hort x' hx'))
    rw [pnorm_ortho X _ _ hx'] at h
    rw [hB x' (hSU (hort x' hx')) b hb, norm_mul]
    exact mul_le_mul (hD b hbC) h (norm_nonneg _) hD0
  obtain ⟨x', hx', b, hb, rfl⟩ := hdec x₁ hx₁
  have hx'' : x' ∈ X.dom := hSU (hort x' hx')
  let u : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => mat x' τ * (mat x₀ τ)⁻¹
  have huu : X.IsUnitaryC u := fun τ v w =>
    unitary_of_gram_eq X τ.1 (hx₀' τ).1 ((hx' τ).trans (hx₀ τ).symm) v w
  have hux : X.lmulC u x₀ = x' := lmulC_div X x₀ x' hx₀'
  obtain ⟨hu1, hu2, hu3⟩ := hu u huu
  have key := integral_mul_ortho X (wtOf X hr c c' n) hx₀ hx₀' hS hSU hu κ hinv hsym hhol hint
    (fun x => F (X.lmulC u x))
    (hF.comp (differentiable_lmulC X u).differentiableOn fun x hx => (hu3 x).2 hx)
    (fun x hx b hb => by rw [lmulC_rmul, hB _ ((hu3 x).2 hx) b hb]) (D * C)
    (fun x hx => hFb _ ((hu2 x).2 hx))
  have h2 : ∫ x in slab X δ, κ x₀ x * F (X.lmulC u x) = ∫ x in slab X δ, κ x' x * F x := by
    rw [← setIntegral_comp_of_stable hS.measurableSet hu1 hu2 (f := fun x => κ x' x * F x)
      (((hcont x' hx'').mul (hF.continuousOn.mono hSU)).aestronglyMeasurable hS.measurableSet)]
    refine setIntegral_congr_fun hS.measurableSet fun x hx => ?_
    beta_reduce
    rw [← hinv u huu x₀ hx₀' x (hSU hx), hux]
  have h3 : ∫ x in slab X δ, κ (rmul x' b) x * F x =
      bchar (wtOf X hr c c' n) b * ∫ x in slab X δ, κ x' x * F x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hS.measurableSet fun x hx => ?_
    beta_reduce
    rw [(hhol x (hSU hx)).2 x' hx'' b hb, mul_assoc]
  rw [h2, hI, hux, hre] at key
  have hk1 : ((κ x₀ x₀).re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk0.ne'
  rw [h3, hB x' hx'' b hb, Complex.ofReal_div, (eq_div_iff hk1).2 key]
  ring

end GlobalTheory.SW
