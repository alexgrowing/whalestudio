import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory

theorem ddcForm_extTrace_eq_rank_two
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (hm : Fintype.card m = 1) (hl : Fintype.card l = 1)
    (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η)
    (hd : ∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
      chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂)
    (ξ₁ η₁ ξ₂ η₂ : V) :
    ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
      chernTwo H z ξ₁ η₁ ξ₂ η₂ - wedge (chernOne (gramS H) z) (chernOne (gramQ H) z) ξ₁ η₁ ξ₂ η₂ := by
  have hz : ∀ {n : Type} [Fintype n] [DecidableEq n], Fintype.card n = 1 →
      ∀ G : V → Matrix n n ℂ, chernTwo G z ξ₁ η₁ ξ₂ η₂ = 0 := by
    intro n _ _ hn G
    have hs : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp hn.le
    have h : ∀ a b : n, curvMinor G z a b ξ₁ η₁ ξ₂ η₂ = 0 := fun a b => by
      rw [Subsingleton.elim b a]; exact curvMinor_self G z a ξ₁ η₁ ξ₂ η₂
    simp [chernTwo, h]
  rw [hd, chTwo_eq, chTwo_eq, chTwo_eq, hz hm, hz hl]
  simp only [wedge, hc]
  ring

end GlobalTheory
