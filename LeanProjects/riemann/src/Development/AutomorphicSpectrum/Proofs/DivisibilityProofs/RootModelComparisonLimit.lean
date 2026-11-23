import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConjStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAllStatement

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Root

theorem word_expand (hI : Inputs) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) {σ : Type} [Fintype σ] [DecidableEq σ]
    {d : ℕ} (hd : IsArithVar M.P d) (ℓ : σ → HermLine M.ι) (n : Fin d → σ → ℤ) (L : Fin d → HermLine M.ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (hℓ : ∀ a, IsSmoothHerm (ℓ a))
    (ha : ∀ j, (L j).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)).a)
    (hh : ∀ j, ∀ z ∈ mcPts M.P, (L j).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)).h z) :
    II _ _ M.P d L = ∑ u : Fin d → σ, (∏ k, (n k (u k) : ℝ)) * II _ _ M.P d (fun k => ℓ (u k)) := by
  have hc : ∀ j, IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)) := fun j =>
    (GlobalTheory.T.hermitian_combination_smooth_conj _ M.ι σ ℓ (n j)).1 hℓ
  rw [hI.metricLocal _ M.ι (II _ M.ι) (hII.1 _ M.ι) M.P d L (fun j => GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)) hd hL hc ha hh]
  exact GlobalTheory.T.arith_intersection_multilinear_all II hII _ M.ι M.P d σ ℓ n hd hℓ

theorem cmp_root : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M₁ M₂ : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (σ : Type) [Fintype σ] [DecidableEq σ] (ℓ₁ : ℝ → σ → HermLine M₁.ι) (ℓ₂ : ℝ → σ → HermLine M₂.ι) (n : Ψ × Fin N → σ → ℤ) (s : Ψ × Fin N → Ψ × Fin N) (e₁ e₂ : ℕ), e₁ ≠ 0 → e₁ * M₁.δ = e₂ * M₂.δ → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (ℓ₁ t a) ∧ IsSmoothHerm (ℓ₂ t a)) ∧ (∀ r, (M₁.x t (s r)).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).a ∧ ∀ z ∈ mcPts M₁.P, (M₁.x t (s r)).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).h z) ∧ ∀ r, (M₂.x t r).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).a ∧ ∀ z ∈ mcPts M₂.P, (M₂.x t r).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).h z) → (∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ, Tendsto (fun t => (e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (w j)) - (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (w j))) (𝓝[>] 0) (𝓝 0)) → ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M₁.P _ (fun j => M₁.x t (s (w j))) / M₁.δ - II _ _ M₂.P _ (fun j => M₂.x t (w j)) / M₂.δ) (𝓝[>] 0) (𝓝 0) := by
  intro hI II hII Ψ _ _ N M₁ M₂ σ _ _ ℓ₁ ℓ₂ n s e₁ e₂ he₁ hδ hev hnull w
  have hδ₁ : (M₁.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M₁.δ_pos.ne'
  have hδ₂ : (M₂.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M₂.δ_pos.ne'
  have he₁' : (e₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he₁
  have hδR : (e₁ : ℝ) * M₁.δ = e₂ * M₂.δ := by exact_mod_cast hδ
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ))
    (fun u _ => (hnull u).const_mul (∏ k, (n (w k) (u k) : ℝ)))
  have hdiv := hsum.const_mul (((e₁ : ℝ) * M₁.δ)⁻¹)
  simp only [mul_zero, Finset.sum_const_zero] at hdiv
  refine Tendsto.congr' ?_ hdiv
  filter_upwards [hev] with t ht
  obtain ⟨hsm, h1, h2⟩ := ht
  have E₁ := word_expand hI II hII M₁ M₁.arith (ℓ₁ t) (fun k => n (w k)) (fun j => M₁.x t (s (w j)))
    (fun j => M₁.x_smooth t _) (fun a => (hsm a).1) (fun j => (h1 (w j)).1) (fun j => (h1 (w j)).2)
  have E₂ := word_expand hI II hII M₂ M₂.arith (ℓ₂ t) (fun k => n (w k)) (fun j => M₂.x t (w j))
    (fun j => M₂.x_smooth t _) (fun a => (hsm a).2) (fun j => (h2 (w j)).1) (fun j => (h2 (w j)).2)
  rw [E₁, E₂]
  have hsplit : ∀ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
      (∏ k, (n (w k) (u k) : ℝ)) * ((e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j)) -
        (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) =
      (e₁ : ℝ) * ((∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j))) -
        (e₂ : ℝ) * ((∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) := fun u => by ring
  simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  generalize (∑ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
    (∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j))) = A
  generalize (∑ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
    (∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) = B
  have hB : (e₂ : ℝ) * B / ((e₁ : ℝ) * M₁.δ) = B / M₂.δ := by
    rw [hδR]
    have he₂ : (e₂ : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hδR
      exact mul_ne_zero he₁' hδ₁ hδR
    field_simp
  rw [← hB]
  field_simp

end GlobalTheory.CompanionTheory.Ar.Cmp.Root
