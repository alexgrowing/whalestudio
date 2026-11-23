import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAdd
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.ProdImWirt
variable {Φ : Type} [Fintype Φ]

noncomputable def mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) (z : Φ → ℂ) : ℂ :=
  c σ * Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ))

theorem hasFDerivAt_logIm (τ : Φ) {z : Φ → ℂ} (hz : (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ((Real.log (z τ).im : ℝ) : ℂ))
      (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))) z := by
  have h1 : HasFDerivAt (fun z : Φ → ℂ => (z τ).im) (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)) z :=
    (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)).hasFDerivAt
  have h2 := h1.log hz
  exact ofRealCLM.hasFDerivAt.comp z h2

theorem hasFDerivAt_expo (A : Φ → ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ∑ τ, A τ * ((Real.log (z τ).im : ℝ) : ℂ))
      (∑ τ, A τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ))))) z := by
  have := HasFDerivAt.sum (u := Finset.univ) (fun τ _ => (hasFDerivAt_logIm τ (hz τ)).const_mul (A τ))
  have e : (∑ τ, fun y : Φ → ℂ => A τ * ((Real.log (y τ).im : ℝ) : ℂ)) = fun y => ∑ τ, A τ * ((Real.log (y τ).im : ℝ) : ℂ) := by
    ext y; simp [Finset.sum_apply]
  rw [e] at this; exact this

theorem hasFDerivAt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (mono c a σ)
      (c σ • (Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ)) • ∑ τ, a σ τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))))) z :=
  ((hasFDerivAt_expo (a σ) hz).cexp).const_mul (c σ)

open Classical in
theorem wirt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, 0 < (z τ).im) (τ₀ : Φ) (b : Bool) :
    wirt τ₀ b (mono c a σ) z =
      mono (fun σ => (if b then I else -I) / 2 * c σ * a σ τ₀) (fun σ => a σ - Pi.single τ₀ 1) σ z := by
  have hz' : ∀ τ, (z τ).im ≠ 0 := fun τ => (hz τ).ne'
  rw [wirt, (hasFDerivAt_mono c a σ hz').fderiv]
  simp [mono, Pi.single_apply]
  have hy := hz τ₀
  have e1 : ∀ x, ((if x = τ₀ then (1:ℂ) else 0).im) = 0 := fun x => by split_ifs <;> simp
  have e2 : ∀ x, ((if x = τ₀ then I else 0).im) = if x = τ₀ then 1 else 0 := fun x => by split_ifs <;> simp
  simp only [e1, e2, ofReal_zero, mul_zero, Finset.sum_const_zero, zero_add, apply_ite (fun r : ℝ => (r : ℂ)), ofReal_one, ofReal_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have he : ∑ x, (a σ x - if x = τ₀ then 1 else 0) * ((Real.log (z x).im : ℝ) : ℂ) =
      ∑ x, a σ x * ((Real.log (z x).im : ℝ) : ℂ) - ((Real.log (z τ₀).im : ℝ) : ℂ) := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [he, Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hy]
  have hy' : ((z τ₀).im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  cases b <;> simp <;> field_simp <;> ring

theorem wirtWord_mono (U : Set (Φ → ℂ)) (hU : IsOpen U) (hUpos : ∀ z ∈ U, ∀ τ, 0 < (z τ).im) (w : List (Φ × Bool)) :
    ∀ (c : ℂ → ℂ) (a : ℂ → Φ → ℂ), Differentiable ℂ c → (∀ τ, Differentiable ℂ (fun σ => a σ τ)) →
      ∃ (c' : ℂ → ℂ) (a' : ℂ → Φ → ℂ), Differentiable ℂ c' ∧ (∀ τ, Differentiable ℂ (fun σ => a' σ τ)) ∧
        ∀ σ, Set.EqOn (wirtWord w (mono c a σ)) (mono c' a' σ) U := by
  induction w with
  | nil => exact fun c a hc ha => ⟨c, a, hc, ha, fun σ z _ => rfl⟩
  | cons l w ih =>
    intro c a hc ha
    obtain ⟨c₁, a₁, hc₁, ha₁, h₁⟩ := ih c a hc ha
    classical
    refine ⟨fun σ => (if l.2 then I else -I) / 2 * c₁ σ * a₁ σ l.1, fun σ => a₁ σ - Pi.single l.1 1,
      ((differentiable_const _).mul hc₁).mul (ha₁ l.1), fun τ => ?_, fun σ z hz => ?_⟩
    · simp only [Pi.sub_apply]
      exact (ha₁ τ).sub (differentiable_const _)
    · rw [wirtWord_cons, GoodAdd.wirt_congr hU (h₁ σ) _ _ hz]
      convert wirt_mono c₁ a₁ σ (hUpos z hz) l.1 l.2

theorem mono_differentiable {c : ℂ → ℂ} {a : ℂ → Φ → ℂ} (hc : Differentiable ℂ c)
    (ha : ∀ τ, Differentiable ℂ (fun σ => a σ τ)) (z : Φ → ℂ) : Differentiable ℂ (fun σ => mono c a σ z) := by
  unfold mono
  refine hc.mul (Differentiable.cexp ?_)
  exact Differentiable.fun_sum fun τ _ => (ha τ).mul (differentiable_const _)

theorem wirtWord_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (w : List (Φ × Bool)) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by
  induction w with
  | nil => exact h
  | cons l w ih => intro y hy; rw [wirtWord_cons, wirtWord_cons]; exact GoodAdd.wirt_congr hU ih _ _ hy

end GlobalTheory.HeckeTwo.ProdImWirt

theorem GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (w : List (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F × Bool)) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F → DifferentiableOn ℂ (fun σ : ℂ => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord w (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) z) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ w z hz
  have hU := GoodAdd.upperHalf_isOpen F
  obtain ⟨c', a', hc', ha', h⟩ := ProdImWirt.wirtWord_mono (upperHalf F) hU (fun z hz => hz) w (fun _ => 1)
    (fun σ _ => -1 - 2 * σ) (differentiable_const _)
    (fun _ => (differentiable_const _).sub ((differentiable_const _).mul differentiable_id))
  have hw : ∀ σ, Set.EqOn (wirtWord w (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)))
      (wirtWord w (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ)) (upperHalf F) := by
    intro σ
    have h0 : Set.EqOn (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))
        (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ) (upperHalf F) := by
      intro y hy
      simp only [ProdImWirt.mono, one_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      have hpos : 0 < (y τ).im := hy τ
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, mul_comm]
    exact ProdImWirt.wirtWord_congr hU h0 w
  refine ((ProdImWirt.mono_differentiable hc' ha' z).differentiableOn).congr fun σ _ => ?_
  rw [hw σ hz, h σ hz]
