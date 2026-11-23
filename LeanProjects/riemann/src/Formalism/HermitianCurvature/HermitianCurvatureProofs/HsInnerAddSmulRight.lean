import Formalism.HermitianCurvature.TopDensNonnegOfKappa

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_add_smul_left (A A' C : Wq →L[ℂ] Wp) (a : ℂ) :
    B.hsInner (A + a • A') C = B.hsInner A C + a * B.hsInner A' C := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, inner_add_right, inner_smul_right, Finset.sum_add_distrib, Finset.mul_sum]

theorem hsInner_add_smul_right (A C C' : Wq →L[ℂ] Wp) (a : ℂ) :
    B.hsInner A (C + a • C') = B.hsInner A C + conj a * B.hsInner A C' := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, inner_add_left, inner_smul_left, Finset.sum_add_distrib, Finset.mul_sum]

end HS

section Forms

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_add_smul (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x x' : Ix S → RadSp k r z z' π π') (a : ℂ) :
    act M (x + a • x') = act M x + a • act M x' := by
  funext e
  simp only [act, Pi.add_apply, Pi.smul_apply, map_add, map_smul, Finset.sum_add_distrib, Finset.smul_sum]

theorem pairAt_add_smul_left (μ : Measure (Mt k r)) (Φ Φ' Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ)
    (h1 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ)
    (h2 : Integrable (fun g : Mt k r => B.hsInner ((Φ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ) :
    pairAt μ (Φ + a • Φ') Ψ c = pairAt μ Φ Ψ c + a * pairAt μ Φ' Ψ c := by
  unfold pairAt
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hsInner_add_smul_left]
  rw [integral_add h1 (h2.const_mul a), integral_const_mul]

theorem pairAt_add_smul_right (μ : Measure (Mt k r)) (Φ Ψ Ψ' : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ)
    (h1 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ)
    (h2 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ) :
    pairAt μ Φ (Ψ + a • Ψ') c = pairAt μ Φ Ψ c + conj a * pairAt μ Φ Ψ' c := by
  unfold pairAt
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hsInner_add_smul_right]
  rw [integral_add h1 (h2.const_mul (conj a)), integral_const_mul]

theorem form_add_smul_left (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u u' y : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ)
    (hin : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hin' : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u' b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hout : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y b) (glue i c c')))
    (hout' : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u' b) (y b) (glue i c c'))) :
    form μ i (u + a • u') y c = form μ i u y c + a * form μ i u' y c := by
  unfold form
  have hpt : (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ ((u + a • u') b) (y b) (glue i c c')) =
      fun c' => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y b) (glue i c c') +
        a * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u' b) (y b) (glue i c c')) := by
    funext c'
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_congr rfl fun b _ => pairAt_add_smul_left μ (u b) (u' b) (y b) _ a (hin c' b) (hin' c' b),
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hpt, integral_add hout (hout'.const_mul a), integral_const_mul]

theorem form_add_smul_right (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u y y' : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ)
    (hin : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hin' : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y' b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hout : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y b) (glue i c c')))
    (hout' : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y' b) (glue i c c'))) :
    form μ i u (y + a • y') c = form μ i u y c + conj a * form μ i u y' c := by
  unfold form
  have hpt : (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) ((y + a • y') b) (glue i c c')) =
      fun c' => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y b) (glue i c c') +
        conj a * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y' b) (glue i c c')) := by
    funext c'
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_congr rfl fun b _ => pairAt_add_smul_right μ (u b) (y b) (y' b) _ a (hin c' b) (hin' c' b),
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hpt, integral_add hout (hout'.const_mul (conj a)), integral_const_mul]

end Forms

theorem formSesqOfInt : FormSesqOfInt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st l0 K hI w hw i c hc x hx x' hx' y hy a
  have hK : ∀ v : Ix S → RadSp P.k P.r z z' π π', v ∈ Submodule.pi Set.univ (fun _ : Ix S => K i) → InK (K i) v :=
    fun v hv b => (Submodule.mem_pi.mp hv) b (Set.mem_univ b)
  have h1 := hI w hw i c hc x y (hK x hx) (hK y hy)
  have h2 := hI w hw i c hc x' y (hK x' hx') (hK y hy)
  have h3 := hI w hw i c hc y x (hK y hy) (hK x hx)
  have h4 := hI w hw i c hc y x' (hK y hy) (hK x' hx')
  constructor
  · show form μ i (act (RRi L st i w) (x + a • x')) y c =
      form μ i (act (RRi L st i w) x) y c + a * form μ i (act (RRi L st i w) x') y c
    rw [act_add_smul]
    exact form_add_smul_left μ i _ _ y c a h1.1 h2.1 h1.2 h2.2
  · show form μ i (act (RRi L st i w) y) (x + a • x') c =
      form μ i (act (RRi L st i w) y) x c + conj a * form μ i (act (RRi L st i w) y) x' c
    exact form_add_smul_right μ i _ x x' c a h3.1 h4.1 h3.2 h4.2

end Formalism.FourierDecayAlt.P5
