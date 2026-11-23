import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

open Matrix MeasureTheory Topology
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem averaging_properness_holds : ACProper := by
  intro k r Wp Wq _ _ _ _ D C C' hC hC' hC'O
  have hW : IsCompact (UWset k r D.z) := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos
  have hW' : IsCompact (UWset k r D.z') := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos
  have hgc : Continuous (B.gN : B.Mat k r → ℝ) := Formalism.FourierDecayAlt.P.B6.gN_continuous
  obtain ⟨MW, hMW⟩ := hW.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MW', hMW'⟩ := hW'.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MC, hMC⟩ := hC.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨Co, hCo0, hCo⟩ := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.orbit D.z D.z' C' hC' hC'O
  have gN_nn : ∀ M : B.Mat k r, 0 ≤ B.gN M := fun M => Real.sqrt_nonneg _
  have bnd : ∀ {s : Set (B.Mat k r)} {M : ℝ}, (∀ x ∈ s, ‖B.gN x‖ ≤ M) → ∀ x ∈ s, B.gN x ≤ M :=
    fun h x hx => (le_abs_self _).trans (h x hx)
  set Bd : ℝ := max MW 0 * max MC 0 * max MW' 0 with hBd
  set R : ℝ := max (max MW MW') (Co * Bd ^ (2 * r + 1)) with hR
  refine ⟨Metric.closedBall 0 (max R 0), isCompact_closedBall _ _, ?_⟩
  intro p hp g hg hsg
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  set h : B.Mat k r := Matrix.of p.1.1
  set n : B.Mat k r := Matrix.of p.1.2
  set h' : B.Mat k r := Matrix.of p.2.1
  set n' : B.Mat k r := Matrix.of p.2.2
  have hdet : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hdet' : IsUnit h'.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1
  have hx : n⁻¹ * g * n' = h * B.sgs p g * h'⁻¹ := by
    have e1 : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e2 : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet'
    calc n⁻¹ * g * n' = (h * h⁻¹) * (n⁻¹ * g * n') * (h' * h'⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = h * (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹ := by simp only [Matrix.mul_assoc]
  have hb : B.gN (n⁻¹ * g * n') ≤ Bd := by
    rw [hx]
    have h1 := bnd hMW h hh
    have h2 := bnd hMC _ hsg
    have h3 := bnd hMW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')
    calc B.gN (h * B.sgs p g * h'⁻¹) ≤ B.gN (h * B.sgs p g) * B.gN h'⁻¹ := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ B.gN h * B.gN (B.sgs p g) * B.gN h'⁻¹ :=
        mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) (gN_nn _)
      _ ≤ max MW 0 * max MC 0 * max MW' 0 :=
        mul_le_mul (mul_le_mul (h1.trans (le_max_left _ _)) (h2.trans (le_max_left _ _)) (gN_nn _) (le_max_right _ _))
          (h3.trans (le_max_left _ _)) (gN_nn _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  have hBd0 : 0 ≤ Bd := by positivity
  have hpow : B.gN (n⁻¹ * g * n') ^ (2 * r + 1) ≤ Bd ^ (2 * r + 1) := pow_le_pow_left₀ (gN_nn _) hb _
  obtain ⟨hon, hon'⟩ := hCo g hg n hn n' hn'
  have hnR : B.gN n ≤ max R 0 :=
    (hon.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hn'R : B.gN n' ≤ max R 0 :=
    (hon'.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hhR : B.gN h ≤ max R 0 :=
    (bnd hMW h hh).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hh'R : B.gN h' ≤ max R 0 :=
    (bnd hMW' h' hh').trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have sup : ∀ x : Mt k r, ‖x‖ ≤ B.gN (Matrix.of x) := fun x => Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN (Matrix.of x)
  rw [mem_closedBall_zero_iff]
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact (sup _).trans hhR
  · exact (sup _).trans hnR
  · exact (sup _).trans hh'R
  · exact (sup _).trans hn'R

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
