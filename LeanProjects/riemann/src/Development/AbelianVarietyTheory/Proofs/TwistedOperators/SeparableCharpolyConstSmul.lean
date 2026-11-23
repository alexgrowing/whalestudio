import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.CentralCharSU

attribute [local instance] GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special

theorem separable_charpoly_const_smul {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : B.charpoly.Separable) : (c • B).charpoly.Separable := by
  let q : Polynomial ℂ := Polynomial.C c⁻¹ * Polynomial.X
  have key : (c • B).charpoly = Polynomial.C (c ^ Fintype.card (Fin n)) * B.charpoly.comp q := by
    have h1 : B.charpoly.comp q = (B.charmatrix.map (Polynomial.compRingHom q)).det := by
      have := RingHom.map_det (Polynomial.compRingHom q) B.charmatrix
      rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, this]
      rfl
    rw [h1, Polynomial.C_pow, ← Matrix.det_smul, Matrix.charpoly]
    congr 1
    ext i j : 1
    have hcc : Polynomial.C c * (Polynomial.C c⁻¹ * Polynomial.X) = (Polynomial.X : Polynomial ℂ) := by
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
    by_cases hij : i = j
    · subst hij
      simp [q, mul_sub, hcc]
    · simp [hij, q]
  have hu : IsUnit (Polynomial.C (c ^ Fintype.card (Fin n))) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc))
  have hu' : IsUnit (Polynomial.C c⁻¹) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hc))
  have h2 : IsCoprime (B.charpoly.comp q) (B.charpoly.derivative.comp q) :=
    IsCoprime.map h (Polynomial.compRingHom q)
  have hq : Polynomial.derivative q = Polynomial.C c⁻¹ := by simp [q]
  rw [key, Polynomial.separable_def, Polynomial.derivative_C_mul, Polynomial.derivative_comp, hq,
    isCoprime_mul_unit_left_left hu, isCoprime_mul_unit_left_right hu, isCoprime_mul_unit_left_right hu']
  exact h2

theorem isRegSS_central_mul {n : ℕ} {ε : Fin n → Bool} {c : SUJ ε} {ζ : ℂ}
    (hc : suMat ε c = ζ • (1 : Matrix (Fin n) (Fin n) ℂ)) {g : SUJ ε} (hg : IsRegSS (suMat ε g)) :
    IsRegSS (suMat ε (c * g)) := by
  have e : suMat ε (c * g) = ζ • suMat ε g := by
    rw [map_mul, hc, Matrix.smul_mul, Matrix.one_mul]
  by_cases hζ : ζ = 0
  · have h01 : (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      have h := congrArg (· * suMat ε c⁻¹) hc
      simp only [← map_mul, mul_inv_cancel, map_one, hζ, zero_smul, zero_mul] at h
      exact h.symm
    haveI := subsingleton_of_zero_eq_one h01
    rwa [Subsingleton.elim (suMat ε (c * g)) (suMat ε g)]
  · rw [e]
    exact separable_charpoly_const_smul _ ζ hζ hg

theorem continuous_suMat {n : ℕ} (ε : Fin n → Bool) : Continuous (suMat ε) :=
  (isInducing_suMat ε).continuous

theorem charFn_central_mul : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (SUJ ε)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V))
    (h : IsURepOn (SUset ε) π) (Θ : SUJ ε → ℂ), IsCharFn (suMat ε) μ (suRep h) Θ → ∀ (c : SUJ ε) (ζ χ : ℂ),
    suMat ε c = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) → χ ≠ 0 → (∀ v, suRep h c v = χ • v) →
    ∀ g : SUJ ε, IsRegSS (suMat ε g) → Θ (c * g) = χ * Θ g := by
  intro n ε μ _ V _ _ _ π h Θ hΘ c ζ χ hc hχ hv g hg
  haveI := GlobalTheory.DSSU.borelSpace_SUJ ε
  set ρ := suRep h with hρdef
  have hρ : GlobalTheory.OpTrace.IsUnitaryRep ρ := GlobalTheory.Orb.isUnitaryRep_repVia h (suMat_mem ε) (continuous_suMat ε)
  set Θ₂ : SUJ ε → ℂ := fun x => χ⁻¹ * Θ (c * x) with hΘ₂
  have hli : LocallyIntegrable Θ₂ μ := by
    have h0 : LocallyIntegrable (fun x => Θ (c * x)) μ := by
      refine (locallyIntegrable_iff).2 fun K hK => ?_
      have hpre : K = (c * ·) ⁻¹' ((c * ·) '' K) := (Set.preimage_image_eq K (mul_right_injective c)).symm
      rw [hpre]
      exact ((measurePreserving_mul_left μ c).integrableOn_comp_preimage (measurableEmbedding_mulLeft c)).2
        ((locallyIntegrable_iff.1 hΘ.1) _ (hK.image (continuous_mul_left c)))
    exact h0.smul χ⁻¹
  have hcont : ∀ s, IsRegSS (suMat ε s) → ContinuousAt Θ₂ s := fun s hs =>
    continuousAt_const.mul ((hΘ.2.1 (c * s) (isRegSS_central_mul hc hs)).comp (continuous_mul_left c).continuousAt)
  have hΘ₂c : IsCharFn (suMat ε) μ ρ Θ₂ := by
    refine ⟨hli, hcont, fun f hf => ?_⟩
    set f₂ : SUJ ε → ℂ := fun x => f (c⁻¹ * x) with hf₂
    have hf₂m : f₂ ∈ CcMat (suMat ε) := by
      obtain ⟨hs, Φ, hΦ, e⟩ := hf
      refine ⟨hs.comp_homeomorph (Homeomorph.mulLeft c⁻¹), fun x =>
        Φ (fun i j => ∑ k, suMat ε c⁻¹ i k * x k j), ?_, fun x => ?_⟩
      · refine hΦ.comp (contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_)
        exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply_apply ℝ ℂ k j)
      · rw [hf₂]
        simp only [e]
        congr 1
    have hfc : Continuous f := GlobalTheory.Orb.continuous_of_mem_ccSmooth (isInducing_suMat ε).continuous hf
    have hf₂c : Continuous f₂ := GlobalTheory.Orb.continuous_of_mem_ccSmooth (isInducing_suMat ε).continuous hf₂m
    have hop : repOp ρ μ f₂ = χ • repOp ρ μ f := by
      ext v
      rw [hρ.repOp_apply hf₂c hf₂m.1, ContinuousLinearMap.smul_apply, hρ.repOp_apply hfc hf.1, ← hv,
        ← (ρ c).integral_comp_comm (hρ.isRepOp hfc hf.1 v).1,
        ← integral_mul_left_eq_self (fun x => f₂ x • ρ x v) c]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp [hf₂, map_mul, ContinuousLinearMap.mul_apply]
    have hint : ∫ g, f g * Θ₂ g ∂μ = χ⁻¹ * ∫ g, f₂ g * Θ g ∂μ := by
      rw [← integral_mul_left_eq_self (fun x => f₂ x * Θ x) c, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp [hf₂, hΘ₂]
      ring
    have ht := hΘ.2.2 f₂ hf₂m
    rw [hop] at ht
    have he : repOp ρ μ f = χ⁻¹ • (χ • repOp ρ μ f) := by rw [smul_smul, inv_mul_cancel₀ hχ, one_smul]
    rw [he, hint]
    exact ⟨ht.1.smul _, by rw [GlobalTheory.OpTrace.trace_smul, ht.2]⟩
  have hu := GlobalTheory.Orb.IsCharFn.unique (isInducing_suMat ε) hΘ₂c hΘ hg
  simp only [hΘ₂] at hu
  rw [← hu]
  field_simp

end GlobalTheory.CentralCharSU
