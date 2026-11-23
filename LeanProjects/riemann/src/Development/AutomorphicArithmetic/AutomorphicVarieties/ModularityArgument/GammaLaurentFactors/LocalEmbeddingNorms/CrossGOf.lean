import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.PairGOps

noncomputable section

open Polynomial

namespace UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Inf

private lemma zero_of_open {f : ℂ → ℂ} (hf : Differentiable ℂ f) {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (h : ∀ s ∈ U, f s = 0) : f = 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
  have h0 : f =ᶠ[nhds z] 0 := Filter.eventually_of_mem (hU.mem_nhds hz) h
  funext s
  exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) h0 (Set.mem_univ s)

private lemma zero_of_left {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℝ) (h : ∀ s : ℂ, s.re < c → f s = 0) : f = 0 :=
  zero_of_open hf (U := {s : ℂ | s.re < c}) (isOpen_lt Complex.continuous_re continuous_const)
    (z := ((c - 1 : ℝ) : ℂ)) (by simp) h

private lemma zero_of_right {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℝ) (h : ∀ s : ℂ, c < s.re → f s = 0) : f = 0 :=
  zero_of_open hf (U := {s : ℂ | c < s.re}) (isOpen_lt continuous_const Complex.continuous_re)
    (z := ((c + 1 : ℝ) : ℂ)) (by simp) h

private lemma mul_ne {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (f0 : f ≠ 0) (g0 : g ≠ 0) :
    (fun s => f s * g s) ≠ 0 := by
  intro h
  obtain ⟨z, hz⟩ := Function.ne_iff.mp f0
  refine g0 (zero_of_open hg (U := {s | f s ≠ 0}) (isOpen_ne_fun hf.continuous continuous_const) hz fun s hs => ?_)
  exact (mul_eq_zero.mp (congrFun h s)).resolve_left hs

private lemma shift_ne {f : ℂ → ℂ} (f0 : f ≠ 0) : (fun s => f (s + 1)) ≠ 0 := by
  intro h
  apply f0
  funext s
  simpa using congrFun h (s - 1)

private lemma cpow_eq {q : ℝ} (hq : 1 < q) (s : ℂ) :
    (q : ℂ) ^ (-s) = Complex.exp (((-Real.log q : ℝ) : ℂ) * (s + 0)) := by
  have h0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  rw [Complex.cpow_def_of_ne_zero h0, ← Complex.ofReal_log (by linarith)]
  congr 1
  push_cast
  ring

private lemma poly_zero {q : ℝ} (hq : 1 < q) (Q : ℂ[X]) (h : ∀ s : ℂ, Q.eval ((q : ℂ) ^ (-s)) = 0) : Q = 0 := by
  have hl : ((Real.log q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  refine Polynomial.eq_zero_of_infinite_isRoot Q ?_
  refine (Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_
  have hx' : x ≠ 0 := hx
  have := h (-(Complex.log x / (Real.log q : ℝ)))
  rw [cpow_eq hq] at this
  have e : ((-Real.log q : ℝ) : ℂ) * (-(Complex.log x / (Real.log q : ℝ)) + 0) = Complex.log x := by
    rw [Complex.ofReal_neg]
    field_simp
    ring
  rw [e, Complex.exp_log hx'] at this
  exact this

private lemma poly_fun_ne {β : ℂ[X]} (h : β ≠ 0) : (fun s : ℂ => β.eval s) ≠ 0 := fun h0 =>
  h (Polynomial.funext fun s => by simpa using congrFun h0 s)

private lemma fac_eq {q : ℝ} (hq : 1 < q) (c : ℂ) (t : ℝ) (P : ℂ[X]) (s : ℂ) :
    fac c t q P s = c * Complex.exp (t * s) * P.eval ((q : ℂ) ^ (-s)) / P.eval ((q : ℂ) * (q : ℂ) ^ (-s)) ∧
    fac c t q P (s + 1) = c * (Complex.exp (t * s) * Complex.exp t) * P.eval ((q : ℂ)⁻¹ * (q : ℂ) ^ (-s)) /
      P.eval ((q : ℂ) ^ (-s)) := by
  have h0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  constructor
  · rw [fac, sub_eq_add_neg, Complex.cpow_add _ _ h0, Complex.cpow_one]
  · rw [fac, mul_add, mul_one, Complex.exp_add, show (1 : ℂ) - (s + 1) = -s by ring,
      show -(s + 1) = -1 + -s by ring, Complex.cpow_add _ _ h0, Complex.cpow_neg_one]

theorem crossGOf : CrossGOf := by
  rintro ⟨hd, hmul, hc, -, hpe⟩ hind hsec L L' β β' q P P' hq β0 β'0 P1 P'1
    ⟨Z₀, W₀, A₀, B₀, k₀, l₀, m₀, t₀, c₀, dZ₀, dW₀, Z₀0, k₀0, l₀0, hr₀, hl₀⟩
    ⟨Z₁, W₁, A₁, B₁, k₁, l₁, m₁, t₁, c₁, dZ₁, dW₁, Z₁0, k₁0, l₁0, hr₁, hl₁⟩
  have dsh : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → Differentiable ℂ fun s => f (s + 1) := fun hf =>
    hf.comp (differentiable_id.add_const 1)
  have eP : ∀ Q : ℂ[X], IsExp fun s : ℂ => Q.eval ((q : ℂ) ^ (-s)) := fun Q => by
    simp only [cpow_eq hq]
    exact hpe Q _ 0
  have nP : ∀ Q : ℂ[X], Q.eval 0 ≠ 0 → (fun s : ℂ => Q.eval ((q : ℂ) ^ (-s))) ≠ 0 := fun Q hQ h =>
    hQ (by rw [poly_zero hq Q fun s => congrFun h s]; simp)
  have hR : (fun s => k₁ * β'.eval s * W₀ s * Z₁ s - k₀ * β.eval s * W₁ s * Z₀ s) = 0 := by
    refine zero_of_right ?_ (max c₀ c₁) fun s hs => ?_
    · have := β.differentiable
      have := β'.differentiable
      fun_prop
    · obtain ⟨a1, a2⟩ := hr₀ s (lt_of_le_of_lt (le_max_left _ _) hs)
      obtain ⟨b1, b2⟩ := hr₁ s (lt_of_le_of_lt (le_max_right _ _) hs)
      simp only [a1, a2, b1, b2]
      ring
  set R : ℂ[X] := P.comp (C (q : ℂ)⁻¹ * X) * P.comp (C (q : ℂ) * X) * P' ^ 2 with hRdef
  set R' : ℂ[X] := P'.comp (C (q : ℂ)⁻¹ * X) * P'.comp (C (q : ℂ) * X) * P ^ 2 with hR'def
  set E : ℂ[X] := P * P.comp (C (q : ℂ) * X) * P' * P'.comp (C (q : ℂ) * X) with hEdef
  set a : ℂ := k₁ * l₀ * Complex.exp t₀ with ha
  set b : ℂ := k₀ * l₁ * Complex.exp t₁ with hb
  have a0 : a ≠ 0 := mul_ne_zero (mul_ne_zero k₁0 l₀0) (Complex.exp_ne_zero _)
  set U : ℂ → ℂ := fun s => (C a * R).eval ((q : ℂ) ^ (-s)) with hU
  set V : ℂ → ℂ := fun s => (C b * R').eval ((q : ℂ) ^ (-s)) with hV
  have eU : IsExp U := eP _
  have eV : IsExp V := eP _
  have U0 : U ≠ 0 := nP _ (by simpa [hRdef, eval_comp, P1, P'1] using a0)
  have E0 := nP E (by simp [hEdef, eval_comp, P1, P'1])
  have dE := hd _ (eP E)
  set c : ℝ := -(max c₀ c₁) - 1 with hcdef
  have l0 : ∀ s : ℂ, s.re < c → s.re < -c₀ ∧ s.re < -c₁ ∧ (s + 1).re < -c₁ := fun s hs => by
    have := le_max_left c₀ c₁
    have := le_max_right c₀ c₁
    simp only [Complex.add_re, Complex.one_re]
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  have dF : Differentiable ℂ fun s => β'.eval s * U s - β.eval s * V s :=
    (β'.differentiable.mul (hd _ eU)).sub (β.differentiable.mul (hd _ eV))
  have dG : Differentiable ℂ fun s => Z₀ s * Z₁ s * Z₁ (s + 1) := (dZ₀.mul dZ₁).mul (dsh dZ₁)
  have G0 : (fun s => Z₀ s * Z₁ s * Z₁ (s + 1)) ≠ 0 :=
    mul_ne (dZ₀.mul dZ₁) (dsh dZ₁) (mul_ne dZ₀ dZ₁ Z₀0 Z₁0) (shift_ne Z₁0)
  have hF : (fun s => β'.eval s * U s - β.eval s * V s) = 0 := by
    by_contra F0
    refine mul_ne (dG.mul dE) dF (mul_ne dG dE G0 E0) F0 (zero_of_left ((dG.mul dE).mul dF) c fun s hs => ?_)
    obtain ⟨s1, s3, s4⟩ := l0 s hs
    obtain ⟨a3, a4⟩ := hl₀ s s1
    obtain ⟨b3, b4⟩ := hl₁ s s3
    obtain ⟨e3, -⟩ := hl₁ (s + 1) s4
    have h := congrFun hR s
    by_contra hne
    simp only [Pi.mul_apply, mul_eq_zero, not_or] at hne
    obtain ⟨⟨⟨⟨n0, n1⟩, n2⟩, n3⟩, n4⟩ := hne
    apply n4
    have y1 : L' (s + 1) ≠ 0 := fun h0 => n2 (by rw [e3, h0]; simp)
    have y2 : L' s ≠ 0 := fun h0 => n0 (by rw [a3, h0]; simp)
    have y3 : B₀ s ≠ 0 := fun h0 => n0 (by rw [a3, h0]; simp)
    have y4 : B₁ s ≠ 0 := fun h0 => n1 (by rw [b3, h0]; simp)
    have y5 : m₀ ≠ 0 := fun h0 => n0 (by rw [a3, h0]; simp [fac])
    have y6 : m₁ ≠ 0 := fun h0 => n1 (by rw [b3, h0]; simp [fac])
    have y7 := Complex.exp_ne_zero (t₀ * s)
    have y8 := Complex.exp_ne_zero (t₁ * s)
    simp only [hEdef, eval_mul, eval_comp, eval_C, eval_X, mul_eq_zero, not_or] at n3
    obtain ⟨⟨⟨z1, z2⟩, z3⟩, z4⟩ := n3
    simp only [a3, a4, b3, b4, Pi.zero_apply, (fac_eq hq _ _ _ s).1, (fac_eq hq _ _ _ s).2] at h
    simp only [hU, hV, hRdef, hR'def, ha, hb, eval_mul, eval_comp, eval_C, eval_X, eval_pow]
    generalize (q : ℂ) ^ (-s) = x at *
    generalize P.eval x = p1 at *
    generalize P'.eval x = p2 at *
    generalize P.eval ((q : ℂ) * x) = p3 at *
    generalize P'.eval ((q : ℂ) * x) = p4 at *
    generalize P.eval ((q : ℂ)⁻¹ * x) = p5 at *
    generalize P'.eval ((q : ℂ)⁻¹ * x) = p6 at *
    have y : L' (s + 1) * L' s * B₀ s * B₁ s * m₀ * m₁ * Complex.exp (t₀ * s) * Complex.exp (t₁ * s) ≠ 0 := by
      simp [y1, y2, y3, y4, y5, y6]
    refine mul_left_cancel₀ y ?_
    have h2 := congrArg (· * (p1 * p2 * p3 * p4)) h
    simp only [zero_mul] at h2
    rw [mul_zero, ← h2]
    field_simp
  obtain ⟨u, v, u0, huv⟩ := hind β' β U V eU eV U0 fun s => sub_eq_zero.mp (congrFun hF s)
  have v0 : v ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (C_ne_zero.mpr u0) β'0 (by simpa using huv)
  have hK : (fun s : ℂ => (C v * (C a * R) - C u * (C b * R')).eval ((q : ℂ) ^ (-s))) = 0 := by
    by_contra K0
    refine mul_ne β.differentiable (hd _ (eP _)) (poly_fun_ne β0) K0 (funext fun s => ?_)
    have h1 := congrFun hF s
    have h2 := congrArg (Polynomial.eval s) huv
    simp only [hU, hV, eval_mul, eval_C, eval_sub, Pi.zero_apply] at h1 h2 ⊢
    linear_combination u * h1 - (a * R.eval ((q : ℂ) ^ (-s))) * h2
  have hK' := poly_zero hq _ fun s => congrFun hK s
  refine hsec q hq P P' (u * b / (v * a)) P1 P'1 ?_
  have hva : (C (v * a) : ℂ[X]) ≠ 0 := C_ne_zero.mpr (mul_ne_zero v0 a0)
  change R = C _ * R'
  clear_value R R' U V a b
  refine mul_left_cancel₀ hva ?_
  rw [← mul_assoc (C (v * a)), ← C_mul, mul_div_cancel₀ _ (mul_ne_zero v0 a0), C_mul (a := v), C_mul (a := u)]
  linear_combination hK'

end UpperTheory.V.Z.Gam
