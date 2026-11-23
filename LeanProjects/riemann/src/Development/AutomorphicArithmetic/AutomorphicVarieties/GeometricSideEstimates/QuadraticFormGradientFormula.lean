import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.AdmissibleFunctionClassClosureProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
open UpperTheory.V.Lit.Geo
open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped ContDiff

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem qf_mem : (fun x : Fin a → Cinf E => ((qf x : ℝ) : ℂ)) ∈ poly E a := by
  have h : (fun x : Fin a → Cinf E => ((qf x : ℝ) : ℂ)) =
      ∑ i : Fin a, ∑ w : InfinitePlace E,
        ((fun x : Fin a → Cinf E => x i w) * (fun x : Fin a → Cinf E => (starRingEnd ℂ) (x i w))) := by
    funext x
    simp only [qf, Finset.sum_apply, Pi.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [h]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun w _ => Subalgebra.mul_mem _ ?_ ?_
  · exact Algebra.subset_adjoin ⟨⟨⟨fun x => x i w, fun _ _ => rfl⟩, fun _ _ => rfl⟩, rfl⟩
  · refine Algebra.subset_adjoin ⟨⟨⟨fun x => (starRingEnd ℂ) (x i w), fun _ _ => ?_⟩, fun c x => ?_⟩, rfl⟩
    · simp
    · simp

private theorem pg_eq (P : (Fin a → Cinf E) → ℂ) :
    pg P = fun x => P x * Complex.exp (-(Real.pi : ℂ) * ((qf x : ℝ) : ℂ)) := by
  funext x
  simp only [pg, gauss]
  push_cast
  rfl

private theorem fderiv_pg {P : (Fin a → Cinf E) → ℂ} (hP : P ∈ poly E a) (x u : Fin a → Cinf E) :
    fderiv ℝ (pg P) x u = (fderiv ℝ P x u - (Real.pi : ℂ) * (P x *
      fderiv ℝ (fun y : Fin a → Cinf E => ((qf y : ℝ) : ℂ)) x u)) * (gauss x : ℝ) := by
  have h1 : HasFDerivAt P (fderiv ℝ P x) x :=
    (((UpperTheory.admissibleFunctionClass_closure_properties E a P hP).1.differentiable (by simp)) x).hasFDerivAt
  have h2 := (((UpperTheory.admissibleFunctionClass_closure_properties E a _ qf_mem).1.differentiable (by simp)) x).hasFDerivAt
  have h3 := h1.mul ((h2.const_mul (-(Real.pi : ℂ))).cexp)
  have hg : ((gauss x : ℝ) : ℂ) = Complex.exp (-(Real.pi : ℂ) * ((qf x : ℝ) : ℂ)) := by
    simp only [gauss]
    push_cast
    rfl
  have h4 := h3.fderiv
  rw [pg_eq, hg]
  erw [h4]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end

theorem UpperTheory.quadratic_form_gradient_formula :
    PolyD := by
  intro E _ _ a P hP
  obtain ⟨hP1, -, hP3⟩ := UpperTheory.admissibleFunctionClass_closure_properties E a P hP
  obtain ⟨hR1, -, hR3⟩ := UpperTheory.admissibleFunctionClass_closure_properties E a _ qf_mem
  refine ⟨?_, ?_, fun T => ?_⟩
  · rw [pg_eq]
    exact hP1.mul (contDiff_const.mul hR1).cexp
  · let b := Module.finBasis ℝ (Fin a → Cinf E)
    obtain ⟨C₀, hC₀, hb⟩ := b.exists_opNorm_le (F := ℂ)
    have hQ : ∀ u : Fin a → Cinf E, ∃ (C : ℝ) (k : ℕ), ∀ x, ‖fderiv ℝ P x u - (Real.pi : ℂ) * (P x *
        fderiv ℝ (fun y : Fin a → Cinf E => ((qf y : ℝ) : ℂ)) x u)‖ ≤ C * (1 + qf x) ^ k := fun u =>
      (UpperTheory.admissibleFunctionClass_closure_properties E a _ (Subalgebra.sub_mem _ ((hP3 0).2.2 u)
        (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hP ((hR3 0).2.2 u)) (Real.pi : ℂ)))).2.1
    choose C k hCk using hQ
    refine ⟨C₀ * ∑ i, |C (b i)|, ∑ i, k (b i), fun x => ?_⟩
    have hq : 1 ≤ 1 + qf x := by linarith [qf_nonneg x]
    have hg : 0 < gauss x := Real.exp_pos _
    have hS : 0 ≤ ∑ i, |C (b i)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have key := hb (u := fderiv ℝ (pg P) x) (M := (∑ i, |C (b i)|) * (1 + qf x) ^ (∑ i, k (b i)) * gauss x)
      (by positivity) (fun i => by
        rw [fderiv_pg hP, norm_mul, Complex.norm_real, Real.norm_of_nonneg hg.le]
        refine mul_le_mul_of_nonneg_right ((hCk (b i) x).trans ?_) hg.le
        refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
        refine mul_le_mul ?_ (pow_le_pow_right₀ hq ?_) (by positivity) hS
        · exact Finset.single_le_sum (f := fun i => |C (b i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        · exact Finset.single_le_sum (f := fun i => k (b i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    calc _ ≤ _ := key
      _ = _ := by ring
  · exact ⟨_, Subalgebra.sub_mem _ (hP3 T).1
      (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hP (hR3 T).1) (Real.pi : ℂ)), fun x => fderiv_pg hP x (T x)⟩
