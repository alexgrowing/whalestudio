import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory

theorem blockQS_curv_eq_neg_dbarHol_extFormAdj {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η := by
  have e1 : blockQS (curv H z ξ η) = -mdbar (fun x => secondForm H x ξ) z η := by
    rw [blockQS_eq, curv]
    ext a b
    simp [secondForm, blockQS_eq, Matrix.toBlocks₂₁]
  have he : (fun x => extFormAdj H x ξ) =ᶠ[𝓝 z] fun x => -secondForm H x ξ := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    exact extFormAdj_eq_neg_secondForm (h.one hx) (h.eventually_herm hx) (h.isUnit x hx)
      (hs x hx) ξ
  rw [e1, dbarHol, neg_neg, mdbar_congr he, mdbar_neg]

end GlobalTheory
