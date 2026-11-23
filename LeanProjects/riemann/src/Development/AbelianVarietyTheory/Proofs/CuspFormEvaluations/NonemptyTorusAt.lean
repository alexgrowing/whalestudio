import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqMulIInfHeightLeCard
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorsLattice
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogThetaSumInvariantSmoothStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeviLogThetaSumStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExists

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

namespace GlobalTheory.ThetaWeight

theorem nonempty_torusAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (w0 : 𝓞 E) (hw : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) :
    ∀ x ∈ X.dom, Nonempty (TorusAt X.toData x) := by
  intro x hx
  obtain ⟨A, -⟩ := GlobalTheory.torusAtExists E r X.toData (fun φ => by
    obtain ⟨u, hu, h⟩ := X.EF_perf (-φ)
    refine ⟨u, hu, fun v => ?_⟩
    have h1 := h v
    rw [EFf, neg_mul, map_neg, AddMonoidHom.neg_apply, Int.cast_neg] at h1
    exact neg_injective h1) w0 hw x hx
  exact ⟨A⟩

theorem exists_weight : TStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → ((∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) ∧ (PT.f E : ℝ) ≤ PT.rd E ∧ (PT.f E : ℝ) ^ 2 ≤ PT.rd E ∧ 16 ≤ PT.rd E ∧ ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ PT.f E ∧ (X.p0 ≤ m ∨ r - X.p0 ≤ m)) → ∃ ps : Frame X.Ψ r → ℝ, IsInvFn X.toData ps ∧ (∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X.toData x0 z)) {z | cpt X.toData x0 z ∈ X.dom}) ∧ (∀ x0 ∈ X.dom, ∀ z, cpt X.toData x0 z ∈ X.dom → ∀ ξ : Fin (nd X.toData) → ℂ, -((r : ℝ) / 2 * leviM X.toData (phla X.toData (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1)) x0 z ξ) ≤ leviM X.toData ps x0 z ξ) ∧ cfwM X.toData ps (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card))) := by
  intro hT E _ _ _ r X hiso ⟨hw, hf1, hf2, hrd, hm⟩
  obtain ⟨ps, hps⟩ : ∃ ps : Frame X.Ψ r → ℝ, ∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) := by
    obtain ⟨w0, hw0⟩ := hw
    have h : ∀ x : Frame X.Ψ r, ∃ t : ℝ, x ∈ X.dom → ∃ A : TorusAt X.toData x, t = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) := by
      intro x
      by_cases hx : x ∈ X.dom
      · obtain ⟨A⟩ := nonempty_torusAt X w0 hw0 x hx
        exact ⟨_, fun _ => ⟨A, rfl⟩⟩
      · exact ⟨0, fun h => absurd h hx⟩
    choose ps hps using h
    exact ⟨ps, hps⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.log_theta_sum_invariant_smooth_alt E r X hiso hw ps hps
  refine ⟨ps, h1, h2, GlobalTheory.T.levi_log_theta_sum_alt E r X hiso hw ps hps, ?_⟩
  obtain ⟨C, A', -, hC⟩ := GlobalTheory.ThetaSumBound.growth_decay hT E r X hiso hf1 hf2 hrd hm
  refine ⟨⟨C, A', fun x hx => ?_⟩, fun η hη _ => ⟨C, A', fun x hx ξ hξ ht => ?_⟩⟩
  · obtain ⟨A, hA⟩ := hps x hx
    rw [hA]
    exact (hC x hx A (GlobalTheory.TupleSumPos.tuple_sum_pos E r X x A)).1
  · obtain ⟨A, hA⟩ := hps x hx
    rw [hA]
    refine ((hC x hx A (GlobalTheory.TupleSumPos.tuple_sum_pos E r X x A)).2 ξ hξ).trans ?_
    have ht0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => zero_le_one.trans (ht τ)
    have ha : 0 ≤ 1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)) := by
      positivity
    generalize 1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)) = a at ha ⊢
    generalize ⨅ τ, X.tt ξ x τ = t at ht0 ⊢
    have := mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hη.le) ha) ht0
    linarith

end GlobalTheory.ThetaWeight
