import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShOfPower
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTotOfPower
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

theorem HeightEvaluation.shSum_lineF (d : IndexData) (u : Idx d → ℚ) :
    (shSum d (lineF d u) : ℝ) = -((d.D : ℝ) + 1) * (degAt d u : ℝ) *
      ∑ τ : Fin d.f, ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) := by
  unfold shSum lineF
  simp only [ShOfPower.proof d]
  push_cast
  rw [Finset.mul_sum]

theorem HeightEvaluation.totSum_lineF (d : IndexData) (u : Idx d → ℚ) :
    (totSum d (lineF d u) : ℝ) = -((d.D : ℝ) + 1) * (degAt d u : ℝ) *
      ∑ τ : Fin d.f, ∑ i : Fin d.N, (u (τ, i) : ℝ) := by
  unfold totSum lineF
  simp only [TotOfPower.proof d]
  push_cast
  rw [Finset.mul_sum]

theorem HeightEvaluation.N_mul_ubar (d : IndexData) (u : Idx d → ℚ) (τ : Fin d.f) :
    (d.N : ℝ) * ubar d (uR d u) τ = ∑ i : Fin d.N, (u (τ, i) : ℝ) := by
  have hN : (d.N : ℝ) ≠ 0 := by
    have := d.two_le_N
    exact_mod_cast (show d.N ≠ 0 by omega)
  unfold ubar uR
  field_simp

theorem HeightEvaluation.proof (h83 : HeightTauIdentity.Statement) : HeightEvaluation.Statement := by
  intro d S hS B0 A0 b0 hA hb u Q hQ
  have key := h83 d S hS B0 A0 b0 hA hb (lineF d u) Q hQ
  have hNu := HeightEvaluation.N_mul_ubar d u
  have first : bigP S B0 u = S.vol * S.hh (lineF d u) + ((d.D : ℝ) + 1) * (S.vol * (degAt d u : ℝ)) *
      ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
        (d.N : ℝ) * b0 * ubar d (uR d u) τ) + restTot S B0 Q := by
    have hsum : ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
        (d.N : ℝ) * b0 * ubar d (uR d u) τ) =
        A0 * ∑ τ : Fin d.f, ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
          b0 * ∑ τ : Fin d.f, ∑ i : Fin d.N, (u (τ, i) : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [← hNu τ]
      ring
    rw [hsum]
    show S.PP B0 (lineF d u) = _
    rw [key, HeightEvaluation.shSum_lineF, HeightEvaluation.totSum_lineF]
    ring
  refine ⟨first, ?_⟩
  have hsum2 : ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
        (d.N : ℝ) * b0 * ubar d (uR d u) τ) =
      ∑ τ : Fin d.f, (A0 * cTau d (uR d u) τ + ((d.j : ℝ) * A0 + (d.N : ℝ) * b0) * ubar d (uR d u) τ) := by
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    unfold cTau uR
    ring
  rw [first, hsum2]

end GroundTheory.Heights₂.Heights.TheoremB
