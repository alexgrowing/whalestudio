import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateVacuumEntireGaussianGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ConjComb

theorem normSq_nonneg (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (La : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    0 ≤ TaylorLogMetric.normSq D T La G := by
  unfold TaylorLogMetric.normSq
  simp only [MeasureTheory.average_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 MeasureTheory.measureReal_nonneg) (MeasureTheory.integral_nonneg fun z => by positivity)

theorem supConst_nonneg (D : D7) (a b : ℕ) : 0 ≤ supConst D a b := by
  have h : 0 ≤ D.host.rdE := by
    exact Real.rpow_nonneg (by positivity) _
  unfold supConst
  positivity

theorem sq_sum_le {k : ℕ} (c f : Fin k → ℂ) (n B : ℝ) (hB : 0 ≤ B) (hc : ∑ i, ‖c i‖ ≤ n) (hf : ∀ i, ‖f i‖ ^ 2 ≤ B) :
    ‖∑ i, c i * f i‖ ^ 2 ≤ n ^ 2 * B := by
  have h1 : ‖∑ i, c i * f i‖ ≤ n * √B := by
    calc ‖∑ i, c i * f i‖ ≤ ∑ i, ‖c i * f i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * √B := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (hf i)) (norm_nonneg _)
      _ = (∑ i, ‖c i‖) * √B := (Finset.sum_mul _ _ _).symm
      _ ≤ n * √B := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
  calc ‖∑ i, c i * f i‖ ^ 2 ≤ (n * √B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = n ^ 2 * B := by rw [mul_pow, Real.sq_sqrt hB]

theorem conj_pres : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ (F₀ F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ), StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F₀ → Pres D (TaylorLogMetric.tor0 D cc dl) L L' F₀ F n → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ F ∧ TaylorLogMetric.CoefIn D F TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D F α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ n ^ 2 * (supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F₀) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl)))) := by
  intro D cc dl t0 hC ht a b L L' hL hL' hev F₀ F n hF₀ hP ρ
  obtain ⟨k, r, y, hr, hy, hn, rfl⟩ := hP
  have h := fun i => GlobalTheory.T.conj_torsion_translate_vacuum_entire_gaussian_growth D cc dl t0 hC ht a b L L' hL hL' hev F₀ hF₀ (y i) (hy i) ρ
  choose h1 h2 F' h3 h4 h5 using h
  have hc : GlobalTheory.ThetaConj.CjF D TaylorLogMetric.Qbar ρ (fun z => ∑ i, r i * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) (y i) F₀ z)
      (fun z => ∑ i, StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (r i) * F' i z) :=
    GlobalTheory.ThetaConj.CjF.sum Finset.univ fun i _ =>
      GlobalTheory.ThetaConj.CjF.mul ⟨h1 i, h3 i, fun α => ⟨h2 i α, h4 i α⟩⟩ (hr i)
  refine ⟨hc.1, fun α => (hc.2.2 α).1, _, hc.2.1, fun α => (hc.2.2 α).2, fun z => ?_⟩
  exact sq_sum_le _ _ n _
    (mul_nonneg (mul_nonneg (supConst_nonneg D a b) (normSq_nonneg _ _ _ _)) (Real.exp_pos _).le) (hn ρ) fun i => h5 i z

end GlobalTheory.ConjComb
