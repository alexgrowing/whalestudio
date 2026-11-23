import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentKaehlerDOfAlgebraicIndependent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_kaehlerD_of_algebraicIndependent : ∀ (k κ : Type) [Field k] [CharZero k] [Field κ] [Algebra k κ] [Algebra.EssFiniteType k κ] {σ : Type} (t : σ → κ), AlgebraicIndependent k t → LinearIndependent κ (fun s => KaehlerDifferential.D k κ (t s)) := by
  first | exact @GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent | exact GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent | (intros; apply GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent <;> assumption)
