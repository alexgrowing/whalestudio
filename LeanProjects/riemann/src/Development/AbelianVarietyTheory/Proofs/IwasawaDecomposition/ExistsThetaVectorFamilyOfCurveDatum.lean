import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TrueTheta

open GlobalTheory.NormSum.UnramHecke GlobalTheory.VacuumScalar

theorem exists_family_of_curve : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ (χ : IdE D → ℂ) (e : FamE D), IsChi D χ ∧ vec22 D (tor0 D cc δ) e ∧ eq22 D (tor0 D cc δ) χ e := by
  intro D cc δ hc
  obtain ⟨t0, ht0⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).1
  obtain ⟨κ, k1, k2, k3⟩ := exists_kappa D
  obtain ⟨χ, hχ, hdet⟩ := exists_chi D κ k1 k2
  have hv : ∀ N N' : ℕ, ∃ e0 : VC D N N' → ℂ, Even (N * N') → oddE0 D cc δ t0 N N' e0 ∧ e0 ≠ 0 := by
    intro N N'
    by_cases h : Even (N * N')
    · obtain ⟨e0, he⟩ := GlobalTheory.Vacuum.exists_vacuum D cc δ hc t0 ht0 N N' h
      exact ⟨e0, fun _ => he⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose e0 he0 using hv
  let e : FamE D := fun N N' L L' =>
    (χ (detId D (stdL D N) L) ^ ((N' / 2 : ℕ) : ℤ) * χ (detId D (stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ))) •
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') (e0 N N')
  have hsc : ∀ {N N' : ℕ} (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L →
      Moves D (g' : GL (Fin N') (AE D)) L' → e N N' L L' = ((scal κ g g' : ℂˣ) : ℂ) •
        Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') (e0 N N') := by
    intro N N' g g' L L' hL hL'
    simp only [e]
    rw [hdet N 1 g _ _ (moves_one D N) hL, hdet N' 1 g' _ _ (moves_one D N') hL', inv_one, inv_one, one_mul, one_mul,
      scal, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
  have hW : ∀ N N', Even N → Even N' → ∃ W : WeilO D cc δ N N' (e0 N N'),
      (∀ τ, 2 * (0 : ℤ) = W.ep * W.chV.n τ + (N : ℤ)) ∧ (∀ τ, 2 * (0 : ℤ) = W.ep' * W.chV'.n τ - (N' : ℤ)) ∧
      ∀ (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L → Moves D (g' : GL (Fin N') (AE D)) L' →
        ((scal κ g g' : ℂˣ) : ℂ) ∈ Qbar ∧ W.Om g g' (e0 N N') = e N N' L L' := by
    intro N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    obtain ⟨W, w1, w2, w3⟩ := k3 cc δ hc N N' hN hN' _ a.1 b
    exact ⟨W, w1, w2, fun g g' L L' hL hL' =>
      ⟨(w3 g g' L L' hL hL').1, by rw [(w3 g g' L L' hL hL').2, hsc g g' L L' hL hL']⟩⟩
  have hTT := fun N N' => (GlobalTheory.ThetaLevels.levels_closed D cc δ hc N N').1
  have hmove : ∀ N N', Even N → Even N' → ∀ (g h : GA D N) (g' h' : GA D N') L L₁ L' L₁',
      Moves D (g : GL (Fin N) (AE D)) L → Moves D (h : GL (Fin N) (AE D)) L₁ →
      Moves D (g' : GL (Fin N') (AE D)) L' → Moves D (h' : GL (Fin N') (AE D)) L₁' →
      e N N' L₁ L₁' = ((scal κ (g⁻¹ * h) (g'⁻¹ * h') : ℂˣ) : ℂ) •
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (e N N' L L') := by
    intro N N' hN hN' g h g' h' L L₁ L' L₁' m1 m2 m3 m4
    obtain ⟨W, -, -, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    obtain ⟨M, hM⟩ := exists_moves (g⁻¹ * h)
    obtain ⟨M', hM'⟩ := exists_moves (g'⁻¹ * h')
    have s0 := sd_of_moves (moves_one D N)
    have s0' := sd_of_moves (moves_one D N')
    have hI := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _ (Or.inr ⟨_, _, s0, s0', rfl⟩)
      (Or.inr ⟨_, _, sd_of_moves hM, sd_of_moves hM', rfl⟩) _ a.1).2.1
    have hio := GlobalTheory.WeilInter.om_iop D cc δ hc (GlobalTheory.InertSign.delta_ne_zero hc) N N' _ W g 1 (g⁻¹ * h) g' 1 (g'⁻¹ * h')
      _ L M L₁ _ L' M' L₁' (moves_one D N) (moves_one D N') (by rwa [mul_one]) (by rwa [mul_one]) hM hM'
      (by rwa [mul_inv_cancel_left]) (by rwa [mul_inv_cancel_left]) _ a.1
    rw [← (w h h' _ _ m2 m4).2, ← (w g g' _ _ m1 m3).2, ← hio]
    conv_lhs => rw [← mul_inv_cancel_left g h, ← mul_inv_cancel_left g' h', W.mul _ _ _ _ _ (hTT N N' _ _ s0 s0' _ a.1),
      (w _ _ _ _ hM hM').2, hsc _ _ _ _ hM hM']
    exact W.smul _ _ _ _ (hTT N N' _ _ (sd_of_moves hM) (sd_of_moves hM') _ hI)
  refine ⟨χ, e, hχ, fun N N' L L' ⟨hN, hN', hL, hL'⟩ => ?_, fun N N' L L' hN hN' γ γ' => ?_,
    fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L hL
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L' hL'
    obtain ⟨W, -, -, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    have hI := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _
      (Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩)
      (Or.inr ⟨_, _, hL, hL', rfl⟩) _ a.1).2.1
    change e N N' L L' ∈ Th D (tor0 D cc δ) L L' ∧ e N N' L L' ≠ 0 ∧ ∃ M : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M
    rw [hsc g g' L L' hg hg']
    exact ⟨GlobalTheory.InertSign.ThSp_smul _ hI, smul_ne_zero (Units.ne_zero _) (lattice_facts hc a.1 b hg hg').1,
      exists_coef_field D cc δ hc t0 ht0 N N' (hN.mul_right _) _ a L L' hL hL' _ (w g g' L L' hg hg').1⟩
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨γA, hγ⟩ := exists_rat γ
    obtain ⟨γA', hγ'⟩ := exists_rat γ'
    obtain ⟨W, w1, w2, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    have hT := hTT N N' _ _ (sd_of_moves (moves_one D N)) (sd_of_moves (moves_one D N')) _ a.1
    have := GlobalTheory.RatEqui.oddEq_of_even D cc δ hc t0 ht0 N N' hN hN' _ a W γA γA' _ _ (fun _ => 0) (fun _ => 0) hγ hγ' w1 w2
      _ (W.maps g g' _ hT)
    change pull D (tor0 D cc δ) _ _ (e N N' _ _) = e N N' _ _
    rw [← (w _ _ _ _ (moves_smulLat hγ hg) (moves_smulLat hγ' hg')).2, W.mul _ _ _ _ _ hT, this, (w _ _ _ _ hg hg').2]
    funext z
    simp
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨h', hh'⟩ := exists_moves_of_selfDual D N' L''.1 L''.2
    change e N N' _ _ = fun z => χ _ ^ _ * Iop D (tor0 D cc δ) _ _ (e N N' _ _) z
    rw [hmove N N' hN hN' g g g' h' _ _ _ _ hg hg hg' hh', hdet _ _ _ _ _ hg' hh', scal, inv_mul_cancel g]
    funext z
    simp
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨h, hh⟩ := exists_moves_of_selfDual D N L₁.1 L₁.2
    change e N N' _ _ = fun z => χ _ ^ _ * Iop D (tor0 D cc δ) _ _ (e N N' _ _) z
    rw [hmove N N' hN hN' g h g' g' _ _ _ _ hg hh hg' hg', hdet _ _ _ _ _ hg hh, scal, inv_mul_cancel g']
    funext z
    simp

end GlobalTheory.TrueTheta
