import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeA.CoefHS

section SlopeTestRemainingChoices

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {ν : Measure Γ} {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem memLp_coef {σ : Γ → (A →L[ℂ] A)} (hσ : IsU σ) {d : ℝ} (hd : IsFd ν σ d) (w v : A) :
    MemLp (fun g => ⟪w, σ g v⟫_ℂ) 2 ν := by
  have hm : AEStronglyMeasurable (fun g => ⟪w, σ g v⟫_ℂ) ν :=
    (continuous_const.inner (hσ.cont v)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine ((hd.2 v w v w).1.norm).congr (.of_forall fun g => ?_)
  simp only [norm_mul, norm_star, sq]

theorem memLp_diag {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) : MemLp (fun g => ⟪v, ρ g v⟫_ℂ) 2 ν := by
  have hc : Continuous fun g => ⟪v, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
  refine (hm.norm.mul_const (‖v‖ * ‖v‖)).mono' (hc.norm.pow 2).aestronglyMeasurable (.of_forall fun g => ?_)
  have h1 : ‖⟪v, ρ g v⟫_ℂ‖ ≤ ‖v‖ * ‖v‖ := (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  rw [Real.norm_of_nonneg (by positivity), norm_star, sq]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

theorem inner_toLp {f g : Γ → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, star (f x) * g x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [RCLike.inner_apply, mul_comm]

theorem orthonormal_coef {σ : Γ → (A →L[ℂ] A)} (hσ : IsU σ) {d : ℝ} (hd : IsFd ν σ d) {ι : Type*} {e : ι → A}
    (he : Orthonormal ℂ e) :
    Orthonormal ℂ fun p : ι × ι => ((√d : ℝ) : ℂ) • (memLp_coef hσ hd (e p.1) (e p.2)).toLp _ := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  have hs : conj ((√d : ℝ) : ℂ) * ((√d : ℝ) : ℂ) = d := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hd.1.le]
  rw [orthonormal_iff_ite]
  rintro ⟨k, l⟩ ⟨k', l'⟩
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, hs, inner_toLp]
  have h := (hd.2 (e l') (e k') (e l) (e k)).2
  have h2 : ∫ x, star ⟪e k, σ x (e l)⟫_ℂ * ⟪e k', σ x (e l')⟫_ℂ ∂ν =
      ⟪e l, e l'⟫_ℂ * ⟪e k', e k⟫_ℂ / (d : ℂ) := by
    rw [← h]
    exact integral_congr_ae (.of_forall fun x => mul_comm _ _)
  simp only []
  rw [h2, orthonormal_iff_ite.1 he l l', orthonormal_iff_ite.1 he k' k]
  by_cases h1 : k = k' <;> by_cases h3 : l = l' <;> simp [h1, h3, hd0, eq_comm]

end SlopeTestRemainingChoices

theorem isHilbertSchmidt_coefOp : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ), IsU ρ → IsFd ν σ d →
    ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    GroundTheory.Automorphic.IsHilbertSchmidt (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hd v hm
  set T := coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm with hT
  let e := GroundTheory.Automorphic.stdHilbertBasis ℂ A
  have hX := memLp_diag hρ v hm
  have hon := orthonormal_coef hσ hd e.orthonormal
  have hsum := Orthonormal.inner_products_summable (hX.toLp _) hon
  have hsd : √d ^ 2 = d := Real.sq_sqrt hd.1.le
  have key : ∀ p : _ × _, ‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2 =
      d⁻¹ * ‖⟪((√d : ℝ) : ℂ) • (memLp_coef hσ hd (e p.1) (e p.2)).toLp _, hX.toLp _⟫_ℂ‖ ^ 2 := by
    intro p
    have h1 : ⟪e p.1, T (e p.2)⟫_ℂ = ⟪hX.toLp _, (memLp_coef hσ hd (e p.1) (e p.2)).toLp _⟫_ℂ := by
      rw [hT, inner_coefOp, inner_toLp]
    rw [h1, inner_smul_left, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hsd, norm_inner_symm, ← mul_assoc, inv_mul_cancel₀ hd.1.ne', one_mul]
  have hs2 : Summable fun p : _ × _ => ‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2 := by
    simp_rw [key]
    exact hsum.mul_left _
  rw [GroundTheory.Automorphic.isHilbertSchmidt_iff e]
  have h3 : ∑' l, ‖T (e l)‖ₑ ^ 2 = ∑' p : _ × _, ENNReal.ofReal (‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2) := by
    simp_rw [GroundTheory.Automorphic.enorm_sq_eq_tsum e (T _)]
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
    refine tsum_congr fun p => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h3]
  exact hs2.tsum_ofReal_lt_top

end GlobalTheory.CompanionTheory.RgHeA.CoefHS

end
