import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffContinuousRapidDecayStatement
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.MoyalPointwise

variable {l : Type} [Fintype l]

def ambU (g g' : Sch l) (p : EuclideanSpace ℝ l) : Sch l :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) g'.hasTemperateGrowth
    (SchwartzMap.compSubConstCLM ℂ (-p) (GlobalTheory.ConjSch.conjSch g))

theorem ambU_apply (g g' : Sch l) (p t : EuclideanSpace ℝ l) :
    ambU g g' p t = starRingEnd ℂ (g (t + p)) * g' t := by
  simp [ambU, SchwartzMap.bilinLeftCLM_apply, GlobalTheory.ConjSch.conjSch_apply, sub_neg_eq_add]

end GlobalTheory.MoyalPointwise

noncomputable section

namespace GlobalTheory.MoyalPointwise

open Complex
open scoped Real RealInnerProductSpace FourierTransform

variable {l : Type} [Fintype l]

theorem integrand_eq (g g' f : Sch l) (x : EuclideanSpace ℝ l) (w : l ⊕ l → ℝ) :
    starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      cexp (((2 * π * ⟪qPart w, x⟫ : ℝ) : ℂ) * I) * 𝓕 (ambU g g' (pPart w)) (qPart w) * f (x + pPart w) := by
  have h1 : ∀ t, starRingEnd ℂ (rhoFun w ⇑g t * starRingEnd ℂ (g' t)) =
      cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) *
        (cexp (((-2 * π * ⟪t, qPart w⟫ : ℝ) : ℂ) * I) • ambU g g' (pPart w) t) := by
    intro t
    rw [ambU_apply, smul_eq_mul, rhoFun, phase, map_mul, map_mul, Complex.conj_conj, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    have e : cexp (((2 * π * ⟪qPart w, t⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * -I) =
        cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) * cexp (((-2 * π * ⟪t, qPart w⟫ : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add, real_inner_comm t (qPart w)]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  have h2 : 𝓕 (ambU g g' (pPart w)) (qPart w) =
      ∫ t, cexp (((-2 * π * ⟪t, qPart w⟫ : ℝ) : ℂ) * I) • ambU g g' (pPart w) t := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  have h3 : starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) =
      cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) * 𝓕 (ambU g g' (pPart w)) (qPart w) := by
    rw [← integral_conj, integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul, h2]
  have key : cexp (((-π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) *
      cexp (((2 * π * ⟪qPart w, x⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I) =
      cexp (((2 * π * ⟪qPart w, x⟫ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h3, rhoFun, phase]
  linear_combination (𝓕 (ambU g g' (pPart w)) (qPart w) * f (x + pPart w)) * key

theorem measurePreserving_pq :
    MeasurePreserving (fun w : l ⊕ l → ℝ => (pPart w, qPart w)) volume volume ∧
      MeasurableEmbedding (fun w : l ⊕ l → ℝ => (pPart w, qPart w)) := by
  let e : (l ⊕ l → ℝ) ≃ᵐ EuclideanSpace ℝ l × EuclideanSpace ℝ l :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : l ⊕ l => ℝ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (l → ℝ)) (MeasurableEquiv.toLp 2 (l → ℝ)))
  have he : ⇑e = fun w : l ⊕ l → ℝ => (pPart w, qPart w) := rfl
  rw [← he]
  refine ⟨?_, e.measurableEmbedding⟩
  exact ((PiLp.volume_preserving_toLp l).prod (PiLp.volume_preserving_toLp l)).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : l ⊕ l => ℝ))

theorem integral_phase_fourier (u : Sch l) (x : EuclideanSpace ℝ l) :
    ∫ q, cexp (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * I) * 𝓕 u q = u x := by
  have h := congrFun (u.continuous.fourierInv_fourier_eq u.integrable (𝓕 u).integrable) x
  rw [Real.fourierInv_eq'] at h
  simpa [SchwartzMap.fourier_coe] using h

theorem moyal_pointwise : ∀ (n : ℕ) (f g g' : Sch (Fin n)) (x : EuclideanSpace ℝ (Fin n)),
    ∫ w : Fin n ⊕ Fin n → ℝ, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      (∫ t, f t * starRingEnd ℂ (g t)) * g' x := by
  intro n f g g' x
  obtain ⟨hmp, hme⟩ := measurePreserving_pq (l := Fin n)
  set G : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℂ := fun z =>
    cexp (((2 * π * ⟪z.2, x⟫ : ℝ) : ℂ) * I) * 𝓕 (ambU g g' z.1) z.2 * f (x + z.1) with hG
  have hI : (fun w : Fin n ⊕ Fin n → ℝ =>
      starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x) =
      G ∘ fun w => (pPart w, qPart w) := by
    funext w
    exact integrand_eq g g' f x w
  have hint : Integrable (fun w : Fin n ⊕ Fin n → ℝ =>
      starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x) := by
    obtain ⟨hc, hd⟩ := GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g'
    obtain ⟨C, hC⟩ := hd (2 * n + 1)
    have hr : (Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      push_cast
      linarith
    have hB := (integrable_one_add_norm (E := Fin n ⊕ Fin n → ℝ) (μ := volume) hr).const_mul
      (C * SchwartzMap.seminorm ℂ 0 0 f)
    have hp : Continuous (fun w : Fin n ⊕ Fin n → ℝ => pPart w) := by
      unfold pPart; fun_prop
    have hq : Continuous (fun w : Fin n ⊕ Fin n → ℝ => qPart w) := by
      unfold qPart; fun_prop
    have hcont : Continuous (fun w : Fin n ⊕ Fin n → ℝ => rhoFun w ⇑f x) := by
      simp only [rhoFun, phase]
      have := f.continuous
      fun_prop
    refine hB.mono' (((Complex.continuous_conj.comp hc).mul hcont).aestronglyMeasurable)
      (.of_forall fun w => ?_)
    have hpos : 0 < 1 + ‖w‖ := by positivity
    have e1 : ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖ ≤ C * (1 + ‖w‖) ^ (-((2 * n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos _)]
      exact hC w
    have e2 : ‖f (x + pPart w)‖ ≤ SchwartzMap.seminorm ℂ 0 0 f := SchwartzMap.norm_le_seminorm ℂ f _
    simp only [Function.comp_apply, norm_mul, RCLike.norm_conj, rhoFun, norm_phase, one_mul]
    calc _ ≤ C * (1 + ‖w‖) ^ (-((2 * n + 1 : ℕ) : ℝ)) * SchwartzMap.seminorm ℂ 0 0 f :=
          mul_le_mul e1 e2 (norm_nonneg _) (le_trans (norm_nonneg _) e1)
      _ = _ := by ring
  have hGint : Integrable G := (hmp.integrable_comp_emb hme).1 (hI ▸ hint)
  calc _ = ∫ w : Fin n ⊕ Fin n → ℝ, G (pPart w, qPart w) := by rw [hI]; rfl
    _ = ∫ z, G z := hmp.integral_comp hme G
    _ = ∫ p, ∫ q, G (p, q) := integral_prod G hGint
    _ = ∫ p, starRingEnd ℂ (g (x + p)) * g' x * f (x + p) := by
        congr 1
        funext p
        simp only [hG]
        rw [integral_mul_const, integral_phase_fourier, ambU_apply]
    _ = ∫ p, (fun y => f y * starRingEnd ℂ (g y)) (x + p) * g' x := by
        congr 1
        funext p
        ring
    _ = _ := by
        rw [integral_mul_const]
        exact congrArg (· * g' x) (integral_add_left_eq_self (fun y => f y * starRingEnd ℂ (g y)) x)

end GlobalTheory.MoyalPointwise
