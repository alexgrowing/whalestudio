import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBigStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates
end GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates
theorem parOf_further_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m,
    (parOf (Fm.L x i) j).b ^ ((4 : ℝ) / 5) ≤ (parOf (Fm.L x i) j).w'' / (parOf (Fm.L x i) j).S ∧
    4 * (parOf (Fm.L x i) j).x ^ 2 * (parOf (Fm.L x i) j).L ^ 2 * (parOf (Fm.L x i) j).b ^ ((4 : ℝ) / 7) <
      (parOf (Fm.L x i) j).b ^ ((4 : ℝ) / 5) := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := ev_large eps he
  refine ⟨x0, fun x hx hle i p _ _ j => ?_⟩
  obtain ⟨hxp, E1, E2, E3, E4⟩ := hx0 x hle
  have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hee : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hsz := Fm.sizes x hx i
  have hN : SizeN (Fm.L x i) := hsz.1
  have hK : SizeK (Fm.L x i) := hsz.2.2.1
  have hD := (Fm.params x hx i).logDel
  have hS := (Fm.L x i).Sc_pos
  rw [(Fm.L x i).Sc_eq] at hS
  unfold SizeN szTh at hN
  unfold SizeK szTh at hK
  rw [hxx, hee] at hN hK hD
  constructor
  · show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 5) ≤
      (Fm.L x i).sc.x * Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) /
        Real.exp ((Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3)) / ((Fm.L x i).sc.x * ((Fm.D x i).R.n : ℝ)) / (Fm.L x i).Sc
    rw [(Fm.L x i).Sc_eq, hxx, hee]
    have hk : (0 : ℝ) ≤ (Fm.D x i).R.k := Nat.cast_nonneg _
    have hn : (0 : ℝ) < (Fm.D x i).R.n := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hN.1
    have hΔ : ((Fm.D x i).s.Del : ℝ) ≤ Real.exp (x ^ (eps / 4) / 2) := by
      have h4 : 0 < 4 * ((Fm.D x i).s.Del : ℝ) := pos_of_mul_pos_right hS hk
      exact (Real.log_le_iff_le_exp (by linarith)).1 hD
    exact w_over_S_real hxp hk hn hS hK.2 hN.2 hΔ E1 E2 E3
  · show 4 * (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ 2 *
        Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 7) <
      Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 5)
    rw [hxx, hee]
    exact pow_real hxp E4
theorem parOf_large_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (parOf (Fm.L x i) j).Large :=
  _root_.GlobalTheory.ExpTie.atPts_mono (_root_.GlobalTheory.ExpTie.atPts_and_alt (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.ExpTie.parOf_hyp_alt _root_.GlobalTheory.T.exists_large_parameter_estimates_at_pts) _root_.GlobalTheory.ExpTie.parOf_further_alt) fun _ _ _ _ _ H j => by
    obtain ⟨⟨hH, hR⟩, hE⟩ := H
    obtain ⟨X', A, hR', hB⟩ := hR j
    exact large_of_rows_pow (hH j) hR' hB (hE j).1 (hE j).2
end GlobalTheory.ExpTie
end
