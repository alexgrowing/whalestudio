import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WaveBallEstimateWeightedDualAlt
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PowFourLeRpowNineHalves
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps

namespace CompanionTheory.WaveGrid.WEnd

open Formalism.FourierDecayAlt BranchingSupport

theorem isDG_of_num {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ} {R : Rep k r}
    (hN : Num k r lam u b bv ga h q0) {ν : Fin (2 * r + k + 1) → ℤ} (hν : n1 ν ≤ q0)
    (hR : R.IsDS (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + (ν a : ℝ)) :
    R.IsDG (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + (ν a : ℝ) := by
  obtain ⟨hc, hds⟩ := hR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgap, hok, -, h2, -⟩ := hN
  refine ⟨hc, hds, h / 4, ?_, hok⟩
  intro a c hac
  show h / 4 ≤ |(lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))|
  have hab : ∀ x : Fin (2 * r + k + 1), |((ν x : ℤ) : ℝ)| ≤ q0 := by
    intro x
    have h1 : (ν x).natAbs ≤ ∑ i, (ν i).natAbs :=
      Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ x)
    have h3 : ((ν x).natAbs : ℝ) ≤ q0 := by exact_mod_cast h1.trans hν
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast h3
  have hg := hgap a c hac
  have hq : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have e1 := le_abs_self ((lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)))
  have e2 := neg_abs_le ((lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)))
  have e3 := le_abs_self ((ν a : ℤ) : ℝ)
  have e4 := neg_abs_le ((ν a : ℤ) : ℝ)
  have e5 := le_abs_self ((ν c : ℤ) : ℝ)
  have e6 := neg_abs_le ((ν c : ℤ) : ℝ)
  have key : |lam a - lam c| ≤ |(lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))| + |((ν a : ℤ) : ℝ)| + |((ν c : ℤ) : ℝ)| :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith [hab a, hab c]

theorem wave_inputs_of_hypotheses_global (H : HypsG) : In91 := by
  unfold In91
  refine ⟨?_, ?_⟩
  · intro k r lam u b bv ga h q0 R0 hN hDS
    have h0 : R0.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (((0 : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) := by
      simpa using hDS
    obtain ⟨R, hR, -⟩ := Gp91.WG.family_through_discreteSeries H k r lam u b bv ga h q0 R0 0 hN
      (isDG_of_num hN (ν := 0) (by simp [BranchingSupport.n1]) h0)
    refine ⟨R, ?_⟩
    intro ν hν
    exact ⟨(hR ν hν).hc, (hR ν hν).ds⟩
  · intro C hC P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 hN hN' hT hT' a R0 f hf
    refine ⟨fun ν₀ hq hDS => ?_, fun j hj hq hDS => ?_⟩
    · have hν : BranchingSupport.n1 ν₀ ≤ q0 := ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans hq
      exact Gp91.WG.bigCellDerivativeExpansion_of_isDS_of_coefOf H C hC P Wp Wq p lam b bv ga h q0 a R0 f ν₀ hN hN' hT hT' hq
        (isDG_of_num hN hν hDS) hf
    · have h0 : R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r)
          (fun s => lam s + (((0 : Fin (2 * P.r + P.k + 1) → ℤ) s : ℤ) : ℝ)) := by
        simpa using hDS
      have hg := isDG_of_num hN (ν := 0) (by simp [BranchingSupport.n1]) h0
      have hg' : R0.IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) lam := by simpa using hg
      exact Gp91.WG.momL_le H C hC P Wp Wq p lam b bv ga h q0 a R0 f j hj hN hN' hT hT' hq hg' hf

end CompanionTheory.WaveGrid.WEnd
