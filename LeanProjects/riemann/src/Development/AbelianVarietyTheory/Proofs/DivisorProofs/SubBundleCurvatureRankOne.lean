import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory.LineRankTwo

theorem chernOne_sub_quot_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H)
    (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1)
    (hg : ∀ ξ η, curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) +
      wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η)
    (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η)
    (u : m → ℂ) (hu : u ≠ 0) (ξ η : V) :
    chernOne (gramS H) z ξ η = lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η ∧
    chernOne (gramQ H) z ξ η =
      chernOne H z ξ η - lineCurv H z (incl m l *ᵥ u) ξ η + extTrace H z ξ η := by
  have hzH : (H z).PosDef := h.posDef z hz
  have hS : (subGram (H z)).PosDef := posDef_subGram hzH
  have hsu : IsUnit (subGram (H z)).det := (isUnit_iff_isUnit_det _).1 hS.isUnit
  have hSu : form (subGram (H z)) u u ≠ 0 := ((posDef_iff.1 hS).2 u hu).ne'
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 hm
  have hvec : ∀ M : Matrix m m ℂ, M *ᵥ u = M.trace • u := by
    intro M
    funext i
    rw [ha i]
    simp only [mulVec, dotProduct, trace, diag, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single a (fun j hj => absurd (ha j) hj),
      Fintype.sum_eq_single a (fun j hj => absurd (ha j) hj)]
  have hline : lineCurv H z (incl m l *ᵥ u) ξ η = kappa * (blockSS (H z) (curv H z ξ η)).trace := by
    have e1 : curv H z ξ η *ᵥ (incl m l *ᵥ u) = incl m l *ᵥ (blockSS (H z) (curv H z ξ η) *ᵥ u) +
        orthLift (H z) *ᵥ (quotMap m l *ᵥ (curv H z ξ η *ᵥ (incl m l *ᵥ u))) := by
      conv_lhs => rw [← Matrix.one_mulVec (curv H z ξ η *ᵥ _), ← incl_mul_orthProj_add (H z)]
      simp only [Matrix.add_mulVec, mulVec_mulVec, blockSS, Matrix.mul_assoc, Matrix.add_mul]
    rw [lineCurv, e1, form_add_left, form_orthLift_incl hsu, add_zero, form_incl, form_incl, hvec,
      form_smul_left, mul_div_assoc, div_self hSu, mul_one]
  have hp : ∀ᶠ x in 𝓝 z, (H x).PosDef :=
    Filter.eventually_of_mem (h.isOpen.mem_nhds hz) fun x hx => h.posDef x hx
  have hext : extTrace H z ξ η = kappa * (secondForm H z ξ * secondFormAdj H z η).trace :=
    extTrace_eq (h.isHermFrame.one hz) hp ξ η
  have h1 : chernOne (gramS H) z ξ η =
      lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η := by
    rw [chernOne, hg, hline, hext, wedgeAntiHol, trace_add, trace_neg,
      trace_mul_comm (secondFormAdj H z η)]
    ring
  refine ⟨h1, ?_⟩
  rw [hc ξ η, h1]
  ring

end GlobalTheory.LineRankTwo
