import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.VacInt

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ}

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h, h1, -⟩ := exists_lattice_of_adelic_point D N
  exact h1 ▸ (h 1).2

theorem vac_mem_TT (hg : admG1 D) (crv : Crv D cc δ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) :
    e0 ∈ TT D (tor0 D cc δ) a d := by
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, (GlobalTheory.ThetaLine.theta_line D hg cc δ crv a d _ (Or.inr ⟨_, _, sd_std D a, sd_std D d, rfl⟩)).2.1 x hx]
  exact funext (he.2 x hx)

theorem om_vac_norm (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) {k : GA D a} {k' : GA D d} (hk : k ∈ intG D a) (hk' : k' ∈ intG D d) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0 := by
  obtain ⟨x, x', -, -, h⟩ := om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk')
  refine ⟨_, ?_, h⟩
  simp [W.chV.unitary, W.chV'.unitary]

theorem om_vac_fix (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) (hu : ∀ u, IntU D u → W.chV'.f u = 1) {k : GA D a} (hk : k ∈ intG D a) :
    W.Om k 1 e0 = e0 := by
  obtain ⟨x, hx, h⟩ := om_vac_left he hT W (AdLattice.intG_of_mem D a k hk)
  rw [h, hu x hx]
  simp

def sphericalPair (hg : admG1 D) (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (had : a ≤ d) (hd : Even d)
    (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0) (n : D.what₂.Tau → ℕ)
    (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) (hu : ∀ u, IntU D u → W.chV'.f u = 1) :
    Pair D cc δ t0 1 :=
  Pair.ofVacuum crv pt0 had hd vac W n wt (fun _ hk => om_vac_fix vac.1 (vac_mem_TT hg crv vac.1) W hu hk)
    (fun _ hj => om_vac_norm vac.1 (vac_mem_TT hg crv vac.1) W (one_mem _) hj)

theorem vacuum_eigen : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (a d : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), ∀ W : WeilO D cc δ a d e0,
      e0 ∈ TT D (tor0 D cc δ) a d ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ x x' : (AE D)ˣ, IntU D x ∧ IntU D x' ∧
        W.Om k k' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) • e0) ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → ∀ k ∈ intG D a, W.Om k 1 e0 = e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → a ≤ d → Even d → ∀ t0 : ℂ, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
        oddE0 D cc δ t0 a d e0 → ∀ n : D.what₂.Tau → ℕ, (∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) →
        ∃ P : Pair D cc δ t0 1, P.a = a ∧ P.d = d ∧ HEq P.e0 e0 ∧ HEq P.W W ∧ P.n = n ∧ P.F = P.e0 ∧ P.F ≠ 0 ∧
          P.J = intG D P.d) := by
  intro D hg cc δ crv a d e0 he W
  have hT := vac_mem_TT hg crv he
  exact ⟨hT, fun k hk k' hk' => om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk'),
    fun _ hk _ hk' => om_vac_norm he hT W hk hk', fun hu _ hk => om_vac_fix he hT W hu hk,
    fun hu had hd t0 pt0 vac n wt => ⟨sphericalPair hg crv pt0 had hd vac W n wt hu, rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl,
      W.nz, rfl⟩⟩

end GlobalTheory.NormSum.VacInt
