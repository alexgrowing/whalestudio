import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivPushForward.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a : MRing (fun k => ι' (j k)) F), IsMultiHomog a c →
    a ∉ contractPrime j P' →
    ∀ (N' : Ideal (MRing ι' F) → ℤ) (N : Ideal (MRing (fun k => ι' (j k)) F) → ℤ),
      (∀ W' (hW' : IsMultiProjPrime W'), relDim W' = (n : ℕ) →
        relDim (contractPrime j W') = (n : ℕ) →
        haveI := hW'.isPrime
        N' W' = relDeg j W' * N (contractPrime j W')) →
      (∀ W', IsMultiProjPrime W' → relDim W' = (n : ℕ) → relDim (contractPrime j W') < (n : ℕ) →
        N' W' = 0) →
      haveI := hP'.isPrime
      cycEval N' (divCycle P' (rename (blockIncl j ι') a)) =
        relDeg j P' * cycEval N (divCycle (contractPrime j P') a)

open Classical in

theorem DivPushForward.hypotheses_example :
    let P' : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ) := ⊥
    let N : Ideal (MRing (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k)) ℚ) → ℤ := fun _ => 1
    let N' : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ) → ℤ := fun W' =>
      if h : W'.IsPrime ∧ relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') = ((0 : ℕ) : WithBot (WithTop ℤ)) then
        haveI := h.1; (relDeg (Function.Embedding.some : Unit ↪ Option Unit) W' : ℤ) * N (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') else 0
    IsMultiProjPrime P' ∧ relDim P' = ((0 + 1 : ℕ) : WithBot (WithTop ℤ)) ∧
      relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) P') = ((0 + 1 : ℕ) : WithBot (WithTop ℤ)) ∧
      IsMultiHomog (X ⟨(), (0 : Fin 2)⟩ : MRing (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k)) ℚ)
        (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), (0 : Fin 2)⟩ : MRing (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k)) ℚ) ∉ contractPrime (Function.Embedding.some : Unit ↪ Option Unit) P' ∧
      (∀ W' (hW' : IsMultiProjPrime W'), relDim W' = ((0 : ℕ) : WithBot (WithTop ℤ)) →
        relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') = ((0 : ℕ) : WithBot (WithTop ℤ)) →
        haveI := hW'.isPrime
        N' W' = relDeg (Function.Embedding.some : Unit ↪ Option Unit) W' * N (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W')) ∧
      (∀ W', IsMultiProjPrime W' → relDim W' = ((0 : ℕ) : WithBot (WithTop ℤ)) →
        relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') < ((0 : ℕ) : WithBot (WithTop ℤ)) → N' W' = 0) := by
  intro P' N N'
  obtain ⟨h1, h2, h3⟩ := ProjectionFormulaDegree.hypotheses_example
  refine ⟨h1, h2, h3, coordinate_isMultiHomog 1 0, ?_, ?_, ?_⟩
  · rw [show P' = ⊥ from rfl, contractPrime_bot, Ideal.mem_bot]
    exact X_ne_zero _
  · intro W' hW' _ hc
    show (if h : _ then _ else _) = _
    rw [dif_pos ⟨hW'.isPrime, hc⟩]
  · intro W' _ _ hc
    show (if h : _ then _ else _) = _
    rw [dif_neg (fun h => (ne_of_lt hc) h.2)]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
