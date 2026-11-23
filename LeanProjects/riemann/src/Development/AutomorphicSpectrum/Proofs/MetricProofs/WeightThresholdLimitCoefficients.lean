import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormula
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormula
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNef
import Development.WeilBound.CoreStatements.FlagImmersions.RootModelLineSemipositive
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem tower_seq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) (u : Wt Ψ N) (g : ℝ) (c : T.Comp) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (Ψ × Fin N) → ℤ), IsFullIntersectionSystem II → T.T1 II → WeightHyp T.j u g → bigB0 u g < B + 1 → (∀ n, 0 < s n) → Tendsto s atTop (𝓝 0) → (∀ n, 0 < q n) → (∀ n j, (m n j : ℝ) = q n * (T.M B c).coef (T.lamS u (s n)) (s n) j) → (∀ᶠ n in atTop, IsNefH (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n))) ∧ Tendsto (fun n => geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / (q n : ℝ) ^ dimFl Ψ N) atTop (𝓝 ((T.M B c).δ * (T.vol c * flagDeg u))) ∧ Tendsto (fun n => normHt II (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / q n) atTop (𝓝 (T.slope II B c u)) ∧ 0 < T.vol c * flagDeg u := by
  intro Ψ _ _ N T II B u g c s q m hII hT1 hW hB hs hs0 hq hm
  obtain ⟨h1, -, h3, h4, h5⟩ := hT1 u g hW B hB c
  have hs' : Tendsto s atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hs0, Eventually.of_forall fun n => hs n⟩
  have hδ : ((T.M B c).δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (T.M B c).δ_pos.ne'
  have hqn : ∀ n, (q n : ℝ) ≠ 0 := fun n => Nat.cast_ne_zero.2 (hq n).ne'
  have hgeo : ∀ n, geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) =
      (T.M B c).δ * (q n : ℝ) ^ dimFl Ψ N * T.mDeg B c u (s n) := by
    intro n
    have := geoFun_comb_mixed II hII Ψ N (T.M B c) (scale (s n)) (fun _ => T.lamS u (s n)) (fun _ => s n) (q n)
      (fun _ => m n) (fun _ j => hm n j)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have har : ∀ n, II (T.M B c).K (T.M B c).ι (T.M B c).P (dimFl Ψ N + 1)
      (fun _ => combLine ((T.M B c).line (scale (s n))) (m n)) =
      (T.M B c).δ * (q n : ℝ) ^ (dimFl Ψ N + 1) * T.mbarTop II B c u (s n) := fun n =>
    top_comb_eq_arFun II hII Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n)
  refine ⟨?_, ?_, ?_, h4⟩
  · filter_upwards [hs'.eventually h1] with n hn
    have a := (nefFib_integral_multiple Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n)).2 hn.1
    have b := RootFieldNumerics.root_model_line_semipositive Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n) hn.2
    exact ⟨⟨_, le_rfl, b.1⟩, b.2, a⟩
  · refine ((h3.comp hs').const_mul ((T.M B c).δ : ℝ)).congr fun n => ?_
    rw [hgeo n]
    have := hqn n
    simp only [Function.comp]
    field_simp
  · refine (h5.comp hs').congr fun n => ?_
    unfold normHt
    rw [hgeo n, har n]
    have := hqn n
    simp only [Function.comp]
    by_cases h0 : T.mDeg B c u (s n) = 0
    · simp [h0]
    · have h2 : ((dimFl Ψ N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring

end GlobalTheory.CompanionTheory.Ar.Small
