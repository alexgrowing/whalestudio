import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevInequalityAtOneIndefiniteUnitaryStatement

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.SobHS

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_orthonormal_expansion {ι : Type} [Fintype ι] (f : ι → H) :
    ∃ (m : ℕ) (h : Fin m → H) (φ : ι → Fin m → ℂ), Orthonormal ℂ h ∧ (∀ j, f j = ∑ p, φ j p • h p) ∧
      ∀ j, ∑ p, ‖φ j p‖ ^ 2 = ‖f j‖ ^ 2 := by
  let U : Submodule ℂ H := Submodule.span ℂ (Set.range f)
  haveI : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  let b := stdOrthonormalBasis ℂ U
  let u : ι → U := fun j => ⟨f j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨_, fun p => (b p : H), fun j p => ⟪b p, u j⟫_ℂ, b.orthonormal.comp_linearIsometry U.subtypeₗᵢ,
    fun j => ?_, fun j => b.sum_sq_norm_inner_right (u j)⟩
  have := congrArg Subtype.val (b.sum_repr' (u j))
  simpa using this.symm

theorem integral_sq_sum {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {μ : Measure (UJ ε)} {d : ℝ}
    (hd : IsFdeg μ σ d) {m : ℕ} {h : Fin m → H} (hh : Orthonormal ℂ h) (y : Fin m → H) :
    Integrable (fun g : UJ ε => ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2) μ ∧
      ∫ g : UJ ε, ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 ∂μ = (∑ p, ‖y p‖ ^ 2) / d := by
  have e : ∀ g : UJ ε, ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ) =
      ∑ p, ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g) := by
    intro g
    rw [← Finset.sum_mul_sum, ← star_sum, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  have i1 : ∀ p, Integrable (fun g : UJ ε => ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g)) μ :=
    fun p => integrable_finset_sum _ fun q _ => (hd.2 _ _ _ _).1
  have i2 : Integrable (fun g : UJ ε => ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) μ := by
    simp only [e]
    exact integrable_finset_sum _ fun p _ => i1 p
  refine ⟨by simpa only [RCLike.re_to_complex, Complex.ofReal_re] using i2.re, ?_⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [e]
  rw [integral_finset_sum _ fun p _ => i1 p]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finset_sum _ fun q _ => (hd.2 _ _ _ _).1]
  simp only [(hd.2 _ _ _ _).2, orthonormal_iff_ite.1 hh]
  rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
  simp [inner_self_eq_norm_sq_to_K]

theorem sobolev_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (f x : ι → H) (A : ℝ), 0 ≤ A → (∀ j, Sm ε σ (x j)) → (∀ l ∈ S, ∀ z : ι → ℂ, ‖∑ j, z j • Dw σ l (x j)‖ ^ 2 ≤ A * ∑ j, ‖z j‖ ^ 2) → ‖∑ j, ⟪f j, x j⟫_ℂ‖ ^ 2 ≤ C * A * ∑ j, ‖f j‖ ^ 2 := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨S, C, hS, hC, H1⟩ := GlobalTheory.T.sobolev_inequality_at_one_indefiniteUnitary n ε
  obtain ⟨d, hd⟩ := hσ.2.2.2.1
  have hd0 := hd.1
  refine ⟨S, C * S.length / d, hS, by positivity, fun ι _ f x A hA hx hb => ?_⟩
  obtain ⟨m, h, φ, hh, hf, hφ⟩ := exists_orthonormal_expansion f
  let F : List (Mx n) → Mx n → ℂ := fun l g => ∑ j, ⟪f j, σ g (Dw σ l (x j))⟫_ℂ
  have eF : ∀ l g, F l g = ∑ p, ⟪h p, σ g (∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j))⟫_ℂ := by
    intro l g
    simp only [F, map_sum, map_smul, inner_sum, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hf j, sum_inner]
    simp only [inner_smul_left]
  have hI := fun l => integral_sq_sum hd hh fun p => ∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j)
  simp only [← eF] at hI
  have key := H1 F (fun l _ => continuousOn_finset_sum _ fun j _ =>
      (innerSL ℂ (f j)).continuous.comp_continuousOn (hσ.1.2.2 _)) ?_ fun l _ => (hI l).1
  · have e1 : F [] 1 = ∑ j, ⟪f j, x j⟫_ℂ := by simp only [F, sigma_one hσ.1]; rfl
    rw [e1] at key
    refine key.trans ?_
    have h2 : (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum ≤
        (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).length • ((A * ∑ j, ‖f j‖ ^ 2) / d) := by
      refine List.sum_le_card_nsmul _ _ fun r hr => ?_
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
      rw [(hI l).2]
      refine div_le_div_of_nonneg_right ?_ hd0.le
      refine (Finset.sum_le_sum fun p _ => hb l hl _).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [RCLike.norm_conj, hφ]
    rw [List.length_map, nsmul_eq_mul] at h2
    refine (mul_le_mul_of_nonneg_left h2 hC).trans (le_of_eq ?_)
    ring
  · intro l hl X hX g hg
    have e : ∀ t : ℝ, F l (g * NormedSpace.exp (t • X)) =
        ∑ j, ⟪f j, σ g (σ (NormedSpace.exp (t • X)) (Dw σ l (x j)))⟫_ℂ := fun t => by
      simp only [F, sigma_mul hσ.1 hg (exp_mem_UJ hX t)]
    simp only [e]
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := hasDerivAt_orbit hσ.1 ((hx j).word hσ.1 hl) hX 0
    rw [zero_smul, NormedSpace.exp_zero, sigma_one hσ.1] at h1
    exact (((innerSL ℂ (f j)).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1

end GlobalTheory.TypeSum.SobHS
