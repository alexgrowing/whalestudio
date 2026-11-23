import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.HermFrame

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem secondForm_add_vec (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ ξ' : V) :
    secondForm H z (ξ + ξ') = secondForm H z ξ + secondForm H z ξ' := by
  rw [secondForm_eq, secondForm_eq, secondForm_eq, conn_add_vec]; rfl

theorem secondForm_smul_vec (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V) (c : ℂ) (ξ : V) :
    secondForm H z (c • ξ) = c • secondForm H z ξ := by
  rw [secondForm_eq, secondForm_eq, conn_smul_vec]; rfl

theorem isNonnegForm_extTrace {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}
    (h : IsPosFrame U H) (hz : z ∈ U) : IsNonnegForm (extTrace H z) := by
  have h1 : MContDiffAt 1 H z := h.isHermFrame.one hz
  have hp : ∀ᶠ x in 𝓝 z, (H x).PosDef := Filter.eventually_of_mem (h.isOpen.mem_nhds hz) h.posDef
  have hS : (subGram (H z)).IsHermitian := (posDef_subGram hp.self_of_nhds).isHermitian
  have hQ : (quotGram (H z)).IsHermitian := (posDef_quotGram hp.self_of_nhds).isHermitian
  have e : ∀ ξ η, extTrace H z ξ η = kappa * (secondForm H z ξ * secondFormAdj H z η).trace :=
    extTrace_eq h1 hp
  refine ⟨⟨fun x x' y => ?_, fun c x y => ?_, fun x y y' => ?_, fun c x y => ?_⟩, fun ξ η => ?_,
    fun ξ => ?_⟩
  · simp only [e, secondForm_add_vec, Matrix.add_mul, trace_add, mul_add]
  · simp only [e, secondForm_smul_vec, Matrix.smul_mul, trace_smul, smul_eq_mul]; ring
  · simp only [e, secondFormAdj, adj, secondForm_add_vec, conjTranspose_add, Matrix.mul_add,
      Matrix.add_mul, trace_add, mul_add]
  · simp only [e, secondFormAdj, adj, secondForm_smul_vec, conjTranspose_smul, Matrix.mul_smul,
      Matrix.smul_mul, trace_smul, smul_eq_mul, Complex.star_def]; ring
  · have hk : conj kappa = -kappa := by
      rw [kappa, map_div₀, map_mul, conj_I, Complex.conj_ofReal, map_ofNat]; ring
    have ht : conj (secondForm H z ξ * secondFormAdj H z η).trace =
        (secondForm H z η * secondFormAdj H z ξ).trace := by
      rw [← Complex.star_def, ← trace_conjTranspose]
      simp only [secondFormAdj, adj, conjTranspose_mul, conjTranspose_conjTranspose,
        conjTranspose_nonsing_inv, hS.transpose.eq, hQ.transpose.eq, Matrix.mul_assoc]
      rw [trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e, e, map_mul, hk, ht, neg_mul]
  · have : diagVal (fun _ _ : V => (0 : ℂ)) ξ = 0 := by simp [diagVal]
    rw [this]
    exact diagVal_extTrace_nonneg h1 hp ξ

end GlobalTheory.HermFrame
