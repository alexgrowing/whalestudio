import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem exp_of_deriv (f : ℝ → ℂ) (c : ℂ) (hf : ∀ u, HasDerivAt f (c * f u) u) (t : ℝ) :
    f t = Complex.exp (c * t) * f 0 := by
  have h1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-c * v) * f v) 0 u := fun u => by
    have h2 : HasDerivAt (fun v : ℝ => -c * (v : ℂ)) (-c) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-c)
    exact (h2.cexp.fun_mul (hf u)).congr_deriv (by ring)
  have h3 := is_const_of_deriv_eq_zero (fun u => (h1 u).differentiableAt) (fun u => (h1 u).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h3
  rw [← h3, ← mul_assoc, ← Complex.exp_add]
  simp

section
variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

private noncomputable def sc (t : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))

private theorem sc_zero : sc E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := Units.ext (funext fun _ => by simp [expU])
  rw [sc, h, map_one]

private theorem sc_deriv : HasDerivAt (fun t => toL (sc E a t).val) (oneL E a) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (t : ℂ)) 1 0 := by
    simpa using (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => ?_
  have e : (fun t : ℝ => toL (sc E a t).val i j w) = fun t : ℝ => Complex.exp (t : ℂ) * oneL E a i j w := by
    funext t
    by_cases h : i = j
    · subst h
      simp [sc, toL, oneL, expU, Matrix.scalar_apply]
    · simp [sc, toL, oneL, Matrix.scalar_apply, h]
  rw [e]
  exact (h1.mul_const _).congr_deriv (one_mul _)

end

theorem UpperTheory.V.Lit.Bor.aInv :
    UpperTheory.V.Lit.Bor.AInv := by
  intro E _ _ _ a φ c hφ t g
  have h := exp_of_deriv (fun u => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) c (fun u => by
    have h1 := hasDerivAt_curve φ (g * GlobalTheory.UnitaryBC.splitCentre E a u) (sc E a) (oneL E a) (sc_zero E a) (sc_deriv E a)
    have h2 : lieD (oneL E a) φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) = c * φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) :=
      congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) hφ
    rw [h2] at h1
    have h3 := HasDerivAt.comp_sub_const u u (by rw [sub_self]; exact h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have e := CuspidalL2GL.splitCentre_add (E := E) (a := a) u (x - u)
    rw [add_sub_cancel] at e
    simp only [e, mul_assoc]
    rfl) t
  rw [CuspidalL2GL.splitCentre_comm]
  simpa only [CuspidalL2GL.splitCentre_zero, mul_one] using h
