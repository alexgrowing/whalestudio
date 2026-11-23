import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem rot_nsl (k : ℕ) (x : Matrix (Fin 2) (Fin 2) ℝ) (h1 : x 0 0 ^ 2 + x 0 1 ^ 2 = 1) (hc : x 1 0 = -x 0 1)
    (hd : x 1 1 = x 0 0) : x.det = 1 ∧ ∃ c : ℂ, ∀ F : UpperHalfPlane → ℂ, nsl k F x UpperHalfPlane.I = c * F UpperHalfPlane.I := by
  have hdet : x.det = 1 := by rw [Matrix.det_fin_two, hc, hd]; linear_combination h1
  refine ⟨hdet, ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)), fun F => ?_⟩
  have h1' : (x 0 0 : ℂ) ^ 2 + (x 0 1 : ℂ) ^ 2 = 1 := by exact_mod_cast h1
  have hne : (x 1 0 : ℂ) * Complex.I + x 1 1 ≠ 0 := by
    intro h
    rw [hc, hd] at h
    push_cast at h
    have : (1 : ℂ) = 0 := by
      linear_combination ((x 0 1 : ℂ) * Complex.I + x 0 0) * h - h1' + (x 0 1 : ℂ) ^ 2 * Complex.I_sq
    exact one_ne_zero this
  have hq : ((x 0 0 : ℂ) * Complex.I + x 0 1) / ((x 1 0 : ℂ) * Complex.I + x 1 1) = (UpperHalfPlane.I : UpperHalfPlane) := by
    rw [div_eq_iff hne, hc, hd, UpperHalfPlane.coe_I]
    push_cast
    linear_combination (x 0 1 : ℂ) * Complex.I_sq
  unfold nsl
  rw [hdet, UpperHalfPlane.coe_I, hq]
  rw [sign_one, SignType.coe_one, Complex.ofReal_one, one_mul, UpperHalfPlane.ofComplex_apply]
  simp

private theorem rot_rt (k M : ℕ) (hM : 1 ≤ M) (f : UpperHalfPlane → ℂ) (φ : TR.Sm ℚ 2) (hφ : IsLift k M f φ.1)
    (x : GL (Fin 2) ℝ) (h1 : x.val 0 0 ^ 2 + x.val 0 1 ^ 2 = 1) (hc : x.val 1 0 = -x.val 0 1) (hd : x.val 1 1 = x.val 0 0) :
    ∃ c : ℂ, TR.rt ℚ 2 (upR x) φ = c • φ := by
  obtain ⟨hdet, c, hF⟩ := rot_nsl k x.val h1 hc hd
  refine ⟨c, Subtype.ext (funext fun g => ?_)⟩
  obtain ⟨γ, h, u, hu, rfl⟩ := decomp M hM g
  have e : ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u) * upR x = ratGL ℚ 2 γ * (upR (h * x) * finGL ℚ 2 u) := by
    rw [map_mul, mul_assoc, mul_assoc, ← upR_comm, mul_assoc]
  rw [TR.rt_apply, e, hφ γ _ u hu]
  change _ = c * φ.1 _
  rw [hφ γ h u hu, ← hF, (nslMul k f).1 h.val x.val h.det_ne_zero (by rw [hdet]; exact one_pos)]
  rfl

private theorem orth_cases {a b c d : ℝ} (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1)
    (h3 : a * c + b * d = 0) : (c = -b ∧ d = a) ∨ (c = b ∧ d = -a) := by
  have hD : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    linear_combination (c ^ 2 + d ^ 2) * h1 + h2 - (a * c + b * d) * h3
  rcases mul_eq_zero.1 hD with h | h
  · exact Or.inl ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩
  · exact Or.inr ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩

private def epsG : GL (Fin 2) ℝ :=
  ⟨eps, eps, by simp [eps, Matrix.one_fin_two], by simp [eps, Matrix.one_fin_two]⟩

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.liftK :
    UpperTheory.V.Af.Nf.LiftK := by
  intro k M hM f φ hφ
  have : FiniteDimensional ℂ (Submodule.span ℂ ({φ, TR.rt ℚ 2 (upR epsG) φ} : Set (TR.Sm ℚ 2))) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ({φ, TR.rt ℚ 2 (upR epsG) φ} : Set (TR.Sm ℚ 2)))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨r, rfl⟩
  set x : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.map ev (Unitary.toUnits r) with hx
  have e : TR.cptRep ℚ 2 r φ = TR.rt ℚ 2 (upR x) φ := by rw [hx, upR_ev]; rfl
  have hr : ∀ i j, x.val i 0 * x.val j 0 + x.val i 1 * x.val j 1 = if i = j then 1 else 0 := by
    intro i j
    have h := congrArg (fun m => ev (m i j)) r.2.2
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, map_add, map_mul, Matrix.one_apply] at h
    rw [apply_ite ev, map_one, map_zero] at h
    exact h
  have h1 : x.val 0 0 ^ 2 + x.val 0 1 ^ 2 = 1 := by have := hr 0 0; simp only [if_true] at this; linear_combination this
  have h2 : x.val 1 0 ^ 2 + x.val 1 1 ^ 2 = 1 := by have := hr 1 1; simp only [if_true] at this; linear_combination this
  have h3 : x.val 0 0 * x.val 1 0 + x.val 0 1 * x.val 1 1 = 0 := by simpa using hr 0 1
  change TR.cptRep ℚ 2 r φ ∈ _
  rw [e]
  clear_value x
  rcases orth_cases h1 h2 h3 with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · obtain ⟨c, hc⟩ := rot_rt k M hM f φ hφ x h1 hc hd
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · have hv : (epsG * x).val = !![-x.val 0 0, -x.val 0 1; x.val 1 0, x.val 1 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [epsG, eps, Matrix.mul_apply, Fin.sum_univ_two]
    obtain ⟨c, hc⟩ := rot_rt k M hM f φ hφ (epsG * x) (by rw [hv]; simpa using h1) (by rw [hv]; simpa using hc)
      (by rw [hv]; simpa using hd)
    have e2 : x = epsG * (epsG * x) := by
      rw [← mul_assoc, show epsG * epsG = 1 from Units.ext epsG.val_inv, one_mul]
    rw [e2, map_mul, map_mul, Module.End.mul_apply, hc, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
