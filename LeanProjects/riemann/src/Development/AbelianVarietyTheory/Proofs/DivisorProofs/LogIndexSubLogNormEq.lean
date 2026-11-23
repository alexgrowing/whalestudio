import Mathlib
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormEqRelIndexMul
open NumberField

namespace GlobalTheory

theorem log_relIndex_span_sub_sum_log_eq_neg_log_absNorm (K : Type) [Field K] [NumberField K]
    (I : Submodule (𝓞 K) K) (hI : I.FG) (c : K) (hcI : c ∈ I) (hc : c ≠ 0) :
    Real.log ((Submodule.span (𝓞 K) {c}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) -
        ∑ σ : K →+* ℂ, Real.log ‖σ c‖ =
      -Real.log (FractionalIdeal.absNorm
        (⟨I, FractionalIdeal.isFractional_of_fg hI⟩ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) := by
  set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩ with hA
  set C : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := FractionalIdeal.spanSingleton _ c with hC
  have hle : C ≤ A := FractionalIdeal.spanSingleton_le_iff_mem.2 hcI
  have hC0 : C ≠ 0 := by
    rw [hC, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hc
  have h := Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul A C hC0 hle
  have hCsub : (C : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) {c} := FractionalIdeal.coe_spanSingleton _ c
  have hAsub : (A : Submodule (𝓞 K) K) = I := rfl
  rw [hCsub, hAsub, hC, FractionalIdeal.absNorm_span_singleton] at h
  set r : ℕ := (Submodule.span (𝓞 K) {c}).toAddSubgroup.relIndex I.toAddSubgroup with hr

  have hprod : ∏ σ : K →+* ℂ, ‖σ c‖ = |Algebra.norm ℚ c| := by
    have e := Algebra.norm_eq_prod_embeddings ℚ ℂ c
    have e2 : ∏ σ : K →+* ℂ, σ c = ∏ σ : K →ₐ[ℚ] ℂ, σ c :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
    rw [← norm_prod, e2, ← e, eq_ratCast, Complex.norm_ratCast]
    push_cast; rfl
  have hN0 : Algebra.norm ℚ c ≠ 0 := (Algebra.norm_ne_zero_iff).2 hc
  have hσ : ∀ σ ∈ (Finset.univ : Finset (K →+* ℂ)), ‖σ c‖ ≠ 0 := fun σ _ => by
    simpa using (map_ne_zero σ).2 hc
  have hsum : ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = Real.log ((|Algebra.norm ℚ c| : ℚ) : ℝ) := by
    rw [← Real.log_prod hσ, hprod]
  have hR : ((|Algebra.norm ℚ c| : ℚ) : ℝ) = (r : ℝ) * ((FractionalIdeal.absNorm A : ℚ) : ℝ) := by
    rw [h]; push_cast; ring
  have hne : ((|Algebra.norm ℚ c| : ℚ) : ℝ) ≠ 0 := by
    simpa using hN0
  have hr0 : (r : ℝ) ≠ 0 := by intro h0; rw [hR, h0, zero_mul] at hne; exact hne rfl
  have hA0 : ((FractionalIdeal.absNorm A : ℚ) : ℝ) ≠ 0 := by intro h0; rw [hR, h0, mul_zero] at hne; exact hne rfl
  rw [hsum, hR, Real.log_mul hr0 hA0]
  ring

end GlobalTheory
