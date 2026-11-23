import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HilbertSchmidtBlocks.Change

noncomputable section

open scoped Classical ComplexConjugate

namespace NormHilbertSchmidtBlocks

open Formalism.L2.SG.NormCut

theorem hSBlocks_main : HSBlocks := by
  intro C C' V V' _ _ _ _ _ _ _ A B
  have hS : ∀ {W U : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      [NormedAddCommGroup U] [InnerProductSpace ℂ U] (S T : W →L[ℂ] U),
      inner ℂ (hsV S) (hsV T) =
        ∑ i, inner ℂ (S (stdOrthonormalBasis ℂ W i)) (T (stdOrthonormalBasis ℂ W i)) := by
    intro W U _ _ _ _ _ S T
    simp [hsV, PiLp.inner_apply]
  have hblk : ∀ (T : PiLp 2 (fun _ : C' => V') →L[ℂ] PiLp 2 (fun _ : C => V)) (ρ : C) (ρ' : C') (v : V'),
      blockOf T ρ ρ' v = T (WithLp.toLp 2 (Pi.single ρ' v : C' → V')) ρ := by
    intro T ρ ρ' v
    rfl
  have hch := sum_inner_change (stdOrthonormalBasis ℂ (PiLp 2 (fun _ : C' => V')))
    (fun p : (Σ _ : C', Fin (Module.finrank ℂ V')) =>
      WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V'))
    (parseval_single) A.toLinearMap B.toLinearMap
  simp only [ContinuousLinearMap.coe_coe] at hch
  rw [hS, ← hch, Fintype.sum_sigma]
  simp only [hS]
  simp only [hblk, PiLp.inner_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ' _ => ?_
  rw [Finset.sum_comm]

end NormHilbertSchmidtBlocks
