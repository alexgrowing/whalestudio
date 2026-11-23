import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialSolutionSpaceFiniteDimensioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialEqZeroOfEqOnIooStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimContinuousNormLeOnIccOfDeterminedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAbsDetMulArchimedeanExpScalarCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSpanKilledScalarDerivaStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem hasDerivAt_expCurve (ψ : Sm E a) (g : GA E a) (t : ℝ) :
    HasDerivAt (fun x => ψ.1 (g * expCurve E a x)) ((scalD E a ψ).1 (g * expCurve E a t)) t := by
  have h1 := Central.hasDerivAt_scalar (1 : Cinf E) ψ (g * expCurve E a t)
  have h3 := HasDerivAt.comp_sub_const t t ((sub_self t).symm ▸ h1)
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  have e : expCurve E a x = expCurve E a t * expCurve E a (x - t) := by
    rw [← expCurve_add, add_sub_cancel]
  simp only [Function.comp_apply]
  rw [e, ← mul_assoc]
  rfl

theorem commute_scalD_sub (c c' : ℂ) :
    Commute (scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c) (scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c') :=
  Commute.sub_left ((Commute.refl _).sub_right (Algebra.commute_algebraMap_right c' _))
    (Algebra.commute_algebraMap_left c _)

theorem mem_expSol_of_prod (l : List ℂ) : ∀ (ψ : Sm E a),
    (l.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod ψ = 0 →
    ∀ g : GA E a, (fun x => ψ.1 (g * expCurve E a x)) ∈ expSol l := by
  induction l with
  | nil =>
    intro ψ h g
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at h
    subst h
    exact mem_expSol_nil.2 rfl
  | cons c l ih =>
    intro ψ h g
    refine mem_expSol_cons.2 ⟨fun x => (hasDerivAt_expCurve ψ g x).differentiableAt, ?_⟩
    have hc : Commute (scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c)
        (l.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod :=
      Commute.list_prod_right _ _ fun b hb => by
        obtain ⟨c', -, rfl⟩ := List.mem_map.1 hb
        exact commute_scalD_sub c c'
    have h2 : (l.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod
        ((scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c) ψ) = 0 := by
      rw [List.map_cons, List.prod_cons] at h
      rw [← Module.End.mul_apply, ← hc.eq]; exact h
    have h3 := ih _ h2 g
    have e : deriv (fun x => ψ.1 (g * expCurve E a x)) - c • (fun x => ψ.1 (g * expCurve E a x)) =
        fun x => ((scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c) ψ).1 (g * expCurve E a x) := by
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [(hasDerivAt_expCurve ψ g x).deriv]
      simp [Module.algebraMap_end_apply]
    rw [e]; exact h3

theorem norm_le_of_band_wide : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ (N : ℕ) (c : ℝ), 1 ≤ c → ∃ C : ℝ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ∀ g : GA E a, c⁻¹ ≤ absDetA g → absDetA g ≤ 2 * c → ‖φ.1 g‖ ≤ C * M := by
  intro E _ _ _ a L _ W _ X hX N c hc
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨1, fun φ _ M hM g _ _ => ?_⟩
    have e : g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [one_mul]; exact hM g (e ▸ one_mem_band)
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.harishChandraFiniteFormsGL_span_killed_scalarDerivative E a L W X hX N
  set κ : ℝ := a * Module.finrank ℚ E with hκ
  have hκ0 : 0 < κ := mul_pos (by exact_mod_cast ha) (by exact_mod_cast Module.finrank_pos)
  set ℓ : ℝ := Real.log 2 / κ
  have hℓ : 0 < ℓ := div_pos (Real.log_pos (by norm_num)) hκ0
  have hvan : ∀ f ∈ expSol Λ, (∀ x ∈ Set.Icc 0 ℓ, f x = 0) → f = 0 := fun f hf h0 =>
    GlobalTheory.T.exponentialPolynomial_eq_zero_of_eqOn_Ioo Λ f hf 0 ℓ hℓ fun x hx => h0 x (Set.Ioo_subset_Icc_self hx)
  have hcont : ∀ f ∈ expSol Λ, Continuous f := by
    intro f hf
    cases Λ with
    | nil => rw [mem_expSol_nil.1 hf]; exact continuous_const
    | cons c l => exact (mem_expSol_cons.1 hf).1.continuous
  obtain ⟨C, hC⟩ := GlobalTheory.T.finiteDim_continuous_norm_le_on_Icc_of_determined (expSol Λ) (GlobalTheory.T.exponentialPolynomialSolutionSpace_finiteDimensional Λ) hcont ℓ hℓ hvan (Real.log (2 * c) / κ)
  refine ⟨C, fun φ hφ M hM g hg1 hg2 => ?_⟩
  have hgpos := absDetA_pos g
  set τ : ℝ := Real.log (absDetA g) / κ
  set g1 := g * expCurve E a (-τ)
  have hdet1 : absDetA g1 = 1 := by
    rw [GlobalTheory.T.adelicAbsDet_mul_archimedeanExpScalarCurve, ← hκ, show -τ * κ = -Real.log (absDetA g) by simp only [τ]; field_simp, Real.exp_neg,
      Real.exp_log hgpos, mul_inv_cancel₀ hgpos.ne']
  have hf := mem_expSol_of_prod Λ φ (hΛ φ hφ) g1
  have hband : ∀ x ∈ Set.Icc 0 ℓ, ‖φ.1 (g1 * expCurve E a x)‖ ≤ M := by
    intro x hx
    refine hM _ ⟨?_, ?_⟩
    · rw [GlobalTheory.T.adelicAbsDet_mul_archimedeanExpScalarCurve, hdet1, one_mul, ← hκ]
      exact Real.one_le_exp (mul_nonneg hx.1 hκ0.le)
    · rw [GlobalTheory.T.adelicAbsDet_mul_archimedeanExpScalarCurve, hdet1, one_mul, ← hκ]
      have : x * κ ≤ Real.log 2 := by
        have := hx.2; simp only [ℓ] at this; rwa [le_div_iff₀ hκ0] at this
      calc Real.exp (x * κ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 this
        _ = 2 := Real.exp_log (by norm_num)
  have hτ : τ ∈ Set.Icc (-(Real.log (2 * c) / κ)) (Real.log (2 * c) / κ) := by
    have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
    have l1 : Real.log (absDetA g) ≤ Real.log (2 * c) := Real.log_le_log hgpos hg2
    have l2 : -Real.log c ≤ Real.log (absDetA g) := by
      rw [← Real.log_inv]; exact Real.log_le_log (inv_pos.2 hc0) hg1
    have l3 : Real.log c ≤ Real.log (2 * c) := Real.log_le_log hc0 (by linarith)
    constructor
    · rw [← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hκ0.le
    · exact div_le_div_of_nonneg_right l1 hκ0.le
  have := hC _ hf M hband τ hτ
  have e : g1 * expCurve E a τ = g := by
    simp only [g1]; rw [mul_assoc, ← expCurve_add, neg_add_cancel, expCurve_zero, mul_one]
  simpa only [e] using this

end GlobalTheory.HCF

end
