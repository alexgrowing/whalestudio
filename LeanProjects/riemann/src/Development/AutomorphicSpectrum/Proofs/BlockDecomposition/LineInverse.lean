import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Formalism.GelfandTransference.HadamardGelfand.Highest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyLineUnit

noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem line_inverse {e : Mat n} {δ t s : ℂ} (he : e * e = δ • e) (hs : s * (1 + t * δ) = t) :
    (1 + t • e) * (1 - s • e) = 1 ∧ (1 - s • e) * (1 + t • e) = 1 := by
  have key : t - s - t * s * δ = 0 := by linear_combination -hs
  have key' : t - s - s * t * δ = 0 := by linear_combination -hs
  constructor
  · calc (1 + t • e) * (1 - s • e) = 1 + (t - s - t * s * δ) • e := by
          simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, he, smul_smul, sub_smul]
          abel
      _ = 1 := by rw [key, zero_smul, add_zero]
  · calc (1 - s • e) * (1 + t • e) = 1 + (t - s - s * t * δ) • e := by
          simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, he, smul_smul, sub_smul]
          abel
      _ = 1 := by rw [key', zero_smul, add_zero]

theorem conj_line {lam : Fin n → ℤ} (hD : HolRm lam) {e : Mat n} (B : Mat n) {δ : ℂ} (he : e * e = δ • e) :
    ∀ᶠ t : ℂ in 𝓝 0, Rm lam (1 + t • e) * XA lam B =
      (XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) * Rm lam (1 + t • e) := by
  have hc : ContinuousAt (fun t : ℂ => 1 + t * δ) 0 := by fun_prop
  have hδ : ∀ᶠ t : ℂ in 𝓝 0, 1 + t * δ ≠ 0 := hc.eventually_ne (by simp)
  filter_upwards [eventually_line_unit e, hδ] with t hu hne
  have hs : t / (1 + t * δ) * (1 + t * δ) = t := div_mul_cancel₀ t hne
  obtain ⟨-, hyx⟩ := line_inverse he hs
  have hB' : (1 + t • e) * B * (1 - (t / (1 + t * δ)) • e) =
      B + t • (e * B) + (-(t / (1 + t * δ))) • (B * e) + (-(t * (t / (1 + t * δ)))) • (e * B * e) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      mul_assoc]
    module
  have hcomm : (1 + t • e) * B = ((1 + t • e) * B * (1 - (t / (1 + t * δ)) • e)) * (1 + t • e) := by
    rw [mul_assoc ((1 + t • e) * B), hyx, mul_one]
  rw [conj_XA hD hu hcomm, hB', XA_add, XA_add, XA_add, XA_smul, XA_smul, XA_smul]

theorem comm_XA {lam : Fin n → ℤ} (hD : HolRm lam) {e : Mat n} (B : Mat n) {δ : ℂ} (he : e * e = δ • e) :
    XA lam e * XA lam B - XA lam B * XA lam e = XA lam (e * B) - XA lam (B * e) := by
  have hden : HasDerivAt (fun t : ℂ => 1 + t * δ) δ 0 := by
    simpa using ((hasDerivAt_id' (0:ℂ)).mul_const δ).const_add 1
  have hs : HasDerivAt (fun t : ℂ => t / (1 + t * δ)) 1 0 := by
    have h := (hasDerivAt_id' (0:ℂ)).div hden (by simp)
    refine h.congr_deriv ?_
    simp
  have hts : HasDerivAt (fun t : ℂ => t * (t / (1 + t * δ))) 0 0 := by
    have h := (hasDerivAt_id' (0:ℂ)).mul hs
    refine h.congr_deriv ?_
    simp
  have hprod : ∀ (P Q : ℂ → Matrix (Jd n lam) (Jd n lam) ℂ) (P' Q' : Matrix (Jd n lam) (Jd n lam) ℂ),
      (∀ i k, HasDerivAt (fun t => P t i k) (P' i k) 0) → (∀ k j, HasDerivAt (fun t => Q t k j) (Q' k j) 0) →
      ∀ i j, HasDerivAt (fun t => (P t * Q t) i j) ((P' * Q 0 + P 0 * Q') i j) 0 := by
    intro P Q P' Q' hP hQ i j
    simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun k _ => (hP i k).mul (hQ k j)
  have hR : ∀ i k, HasDerivAt (fun t : ℂ => Rm lam (1 + t • e) i k) (XA lam e i k) 0 :=
    hasDerivAt_line hD e
  have hC : ∀ k j, HasDerivAt (fun _ : ℂ => XA lam B k j)
      ((0 : Matrix (Jd n lam) (Jd n lam) ℂ) k j) 0 := fun k j => by
    simpa using hasDerivAt_const (0:ℂ) (XA lam B k j)
  have hG : ∀ i k, HasDerivAt (fun t : ℂ => (XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) i k) ((XA lam (e * B) - XA lam (B * e)) i k) 0 := by
    intro i k
    have h := ((((hasDerivAt_id' (0:ℂ)).mul_const (XA lam (e * B) i k)).const_add (XA lam B i k)).add
      (hs.neg.mul_const (XA lam (B * e) i k))).add (hts.neg.mul_const (XA lam (e * B * e) i k))
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
    exact h.congr_deriv (by ring)
  ext i j
  have hL := hprod (fun t => Rm lam (1 + t • e)) (fun _ => XA lam B) (XA lam e) 0 hR hC i j
  have hRt := hprod (fun t : ℂ => XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) (fun t => Rm lam (1 + t • e))
      (XA lam (e * B) - XA lam (B * e)) (XA lam e) hG hR i j
  have heq : (fun t : ℂ => (Rm lam (1 + t • e) * XA lam B) i j) =ᶠ[𝓝 0]
      (fun t : ℂ => ((XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) * Rm lam (1 + t • e)) i j) := by
    filter_upwards [conj_line hD B he] with t ht
    exact congrArg (fun M => M i j) ht
  have huniq := hL.unique (hRt.congr_of_eventuallyEq heq)
  simp only [zero_smul, add_zero, Rm_one, mul_zero, mul_one, zero_div, neg_zero, zero_mul] at huniq
  rw [Matrix.sub_apply, huniq, Matrix.add_apply]
  ring

theorem XA_zero (lam : Fin n → ℤ) : XA lam (0 : Mat n) = 0 := by
  simpa using XA_smul lam (0 : ℂ) (0 : Mat n)

theorem xu_glRel : ∀ (n : ℕ) (lam : Fin n → ℤ), HolRm lam → Formalism.HadamardInequality.GlRel (Xu lam) := by
  intro n lam hD a b c d
  have hsq : (Matrix.single a b (1:ℂ) : Mat n) * Matrix.single a b 1 =
      (if b = a then (1:ℂ) else 0) • Matrix.single a b 1 := by
    by_cases h : b = a
    · subst h; rw [if_pos rfl, one_smul, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, zero_smul, Matrix.single_mul_single_of_ne _ _ _ _ h]
  have key := comm_XA hD (Matrix.single c d (1:ℂ)) hsq
  have hEB : XA lam ((Matrix.single a b (1:ℂ) : Mat n) * Matrix.single c d 1) =
      if b = c then XA lam (Matrix.single a d 1) else 0 := by
    by_cases h : b = c
    · subst h; rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, Matrix.single_mul_single_of_ne _ _ _ _ h, XA_zero]
  have hBE : XA lam ((Matrix.single c d (1:ℂ) : Mat n) * Matrix.single a b 1) =
      if d = a then XA lam (Matrix.single c b 1) else 0 := by
    by_cases h : d = a
    · subst h; rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, Matrix.single_mul_single_of_ne _ _ _ _ h, XA_zero]
  simp only [Xu]
  rw [key, hEB, hBE]

end GlobalTheory.CompanionTheory.RmHol
