import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportWordMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm

noncomputable section

open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut.DopComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem dop_eq_sum (z : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) :
    dop z f = ∑ l ∈ z.support, z l • l.foldr lineDer f := by
  funext g
  simp only [dop, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem isSm_sum {ι : Type} (s : Finset ι) (φ : ι → GAd σ J → ℂ) (h : ∀ i ∈ s, IsSm σ J (φ i)) :
    IsSm σ J (∑ i ∈ s, φ i) := by
  intro k γ hγ g
  simp only [Finset.sum_apply]
  exact ContDiff.sum fun i hi => h i hi k γ hγ g

theorem foldr_sum {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {ι : Type} (s : Finset ι)
    (φ : ι → GAd σ J → ℂ) (h : ∀ i ∈ s, IsSm σ J (φ i)) :
    l.foldr lineDer (∑ i ∈ s, φ i) = ∑ i ∈ s, l.foldr lineDer (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := foldr_smul l (0 : ℂ) (0 : GAd σ J → ℂ)
    simpa using this
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, IsSm σ J (φ i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      foldr_add hl (h a (Finset.mem_insert_self _ _)) (isSm_sum s φ hs), ih hs]

theorem dop_dop {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : GAd σ J → ℂ) (hf : IsSm σ J f)
    (w z : List (ℝ → GAd σ J) →₀ ℂ) (hw : ∀ l ∈ w.support, ∀ γ ∈ l, IsRealLine σ J γ)
    (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) :
    IsSm σ J (dop z f) ∧ dop w (dop z f) = dop (wordMul w z) f := by
  have hs : ∀ l ∈ z.support, IsSm σ J (z l • l.foldr lineDer f) :=
    fun l hl => isSm_smul _ (isSm_foldr (hz l hl) hf)
  refine ⟨by rw [dop_eq_sum]; exact isSm_sum _ _ hs, ?_⟩
  rw [dop_eq_sum w, wordMul, Finsupp.sum, dop_sum_comb]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finsupp.sum, dop_sum_comb, dop_eq_sum z, foldr_sum (hw l hl) _ _ hs, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [dop_single, foldr_smul, List.foldr_append]
  funext g
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.UAut.DopComp

end
