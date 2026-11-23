import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangLowerBoundRationalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangUpperBoundDensePointsStatement

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem l1_le_card_mul_of_norm_le_one {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (h : ‖lam‖ ≤ 1) :
    l1 lam ≤ (Fintype.card Ψ : ℝ) * N := by
  have hb : ∀ τ i, |lam τ i| ≤ 1 := fun τ i => by
    have h1 : ‖lam τ‖ ≤ ‖lam‖ := norm_le_pi_norm lam τ
    have h2 : ‖lam τ i‖ ≤ ‖lam τ‖ := norm_le_pi_norm (lam τ) i
    rw [← Real.norm_eq_abs]; linarith
  unfold l1
  calc ∑ τ, ∑ i, |lam τ i| ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hb τ i
    _ = (Fintype.card Ψ : ℝ) * N := by simp

theorem RootTower.isRatWt_lamS {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N) {lam : Wt Ψ N}
    (s : ℚ) (h : IsRatWt lam) : IsRatWt (T.lamS lam s) := by
  intro τ i
  obtain ⟨q1, h1⟩ := h τ i
  obtain ⟨q2, h2⟩ := T.nu_rat τ i
  refine ⟨q1 - s * q2, ?_⟩
  simp only [RootTower.lamS, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
  push_cast; ring

theorem mbarTop_squeeze : SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.I3 → T.I5 II → T.I6 II →
    ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 2 ≤ B → ∀ (c : T.Comp) (lam : Wt Ψ N) (θ : ℝ) (s : ℚ),
      IsRatWt lam → ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) →
      CompactGapsGE T.j c₀ lam → Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) →
      0 ≤ T.mDeg B c lam s →
      |T.mbarTop II B c lam s| ≤ C * Real.log (B / (s : ℝ)) * T.mDeg B c lam s := by
  intro hZ1 hZ2 II hII Ψ _ _ N T hI3 hI5 hI6 c₀ hc₀
  obtain ⟨s₀, hs₀, h3⟩ := hI3 ((Fintype.card Ψ : ℝ) * N)
  obtain ⟨θ₅, hθ₅, C₅, h5⟩ := hI5 c₀ hc₀
  obtain ⟨θ₆, hθ₆, C₆, h6⟩ := hI6 c₀ hc₀
  have hD : (0 : ℝ) ≤ (dimFl Ψ N : ℝ) + 1 := by positivity
  refine ⟨min (min θ₅ θ₆) (min 1 s₀), lt_min (lt_min hθ₅ hθ₆) (lt_min one_pos hs₀),
    ((dimFl Ψ N : ℝ) + 1) * (max C₅ 0 + max C₆ 0),
    mul_nonneg hD (add_nonneg (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro B hB c lam θ s hrat hnorm hθ hθ₀ hs hgap hcg hdom hnef hdeg
  have hθ1 : θ ≤ 1 := le_trans hθ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hθs : θ ≤ s₀ := le_trans hθ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hθ5 : θ ≤ θ₅ := le_trans hθ₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hθ6 : θ ≤ θ₆ := le_trans hθ₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hspos : (0 : ℝ) < s := by rw [hs]; positivity
  have hs1 : (s : ℝ) ≤ 1 := by rw [hs]; nlinarith
  have hss₀ : (s : ℝ) ≤ s₀ := by rw [hs]; nlinarith
  have hl1 : l1 lam ≤ (Fintype.card Ψ : ℝ) * N := l1_le_card_mul_of_norm_le_one lam hnorm
  obtain ⟨hNef, hSemi⟩ := h3 B hB c lam (s : ℝ) hl1 hspos hss₀ hdom hnef
  have hrat' : IsRatWt (T.lamS lam s) := RootTower.isRatWt_lamS T s hrat
  have hlow := h5 B hB c lam θ s hrat hnorm hθ hθ5 hs hgap hcg
  obtain ⟨F, hF, hFpt⟩ := h6 B hB c lam θ s hrat hnorm hθ hθ6 hs hgap hcg
  have hL : ((dimFl Ψ N : ℝ) + 1) * (-(C₅ * Real.log (B / (s : ℝ)))) * T.mDeg B c lam s ≤
      T.mbarTop II B c lam s :=
    GlobalTheory.T.zhang_lower_bound_rational hZ1 II hII Ψ N (T.M B c) (scale s) (T.lamS lam s) s (-(C₅ * Real.log (B / (s : ℝ))))
      hrat' hSemi hNef (fun W hW => hlow W hW)
  have hU : T.mbarTop II B c lam s ≤
      ((dimFl Ψ N : ℝ) + 1) * (C₆ * Real.log B) * T.mDeg B c lam s :=
    GlobalTheory.T.zhang_upper_bound_dense_points hZ2 II hII Ψ N (T.M B c) (scale s) (T.lamS lam s) s (C₆ * Real.log B) F
      hrat' hSemi hNef hF (fun W hW => hFpt W hW)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hlogBs : Real.log B ≤ Real.log (B / (s : ℝ)) :=
    Real.log_le_log hBpos (by rw [le_div_iff₀ hspos]; nlinarith)
  have hLg : 0 ≤ Real.log (B / (s : ℝ)) := le_trans hlogB hlogBs
  have hP : 0 ≤ ((dimFl Ψ N : ℝ) + 1) * Real.log (B / (s : ℝ)) * T.mDeg B c lam s :=
    mul_nonneg (mul_nonneg hD hLg) hdeg
  have hQ : 0 ≤ ((dimFl Ψ N : ℝ) + 1) * Real.log B * T.mDeg B c lam s :=
    mul_nonneg (mul_nonneg hD hlogB) hdeg
  have hQP : ((dimFl Ψ N : ℝ) + 1) * Real.log B * T.mDeg B c lam s ≤
      ((dimFl Ψ N : ℝ) + 1) * Real.log (B / (s : ℝ)) * T.mDeg B c lam s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogBs hD) hdeg
  have k1 := mul_le_mul_of_nonneg_right
    (show C₅ ≤ max C₅ 0 + max C₆ 0 by linarith [le_max_left C₅ 0, le_max_right C₆ 0]) hP
  have k2 := mul_le_mul_of_nonneg_right (le_max_left C₆ 0) hQ
  have k3 := mul_le_mul_of_nonneg_left hQP (le_max_right C₆ 0)
  have k4 := mul_le_mul_of_nonneg_right
    (show max C₆ 0 ≤ max C₅ 0 + max C₆ 0 by linarith [le_max_right C₅ 0]) hP
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.CompanionTheory.Ar.Top
