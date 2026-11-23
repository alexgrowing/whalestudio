import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfIsDomainMuNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSandwichTraceEqStatement

noncomputable section

open WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_actH_eq_trace_actT : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ) (a : Λ), (actH D a).trace = (actT D a).trace ∧ (actT D a).trace = padicToO p O (D.ρT a).trace := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D a
  obtain ⟨hdom, hmu⟩ := GlobalTheory.T.ainf_isDomain_mu_ne_zero p C v O hv ε hε
  haveI := hdom
  obtain ⟨-, -, htr⟩ := GlobalTheory.T.matrix_sandwich_trace_eq (Ainf p O) h (mu ε) D.F D.G
    ((D.ρT a).map (ofPadic p O)) (D.ρM a) hmu D.G_mul_F (D.F_act a)
  have hT : (actT D a).trace = fontaineTheta O p (((D.ρT a).map (ofPadic p O)).trace) := by
    simp only [actT, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum, padicToO,
      RingHom.comp_apply]
  have hH : (actH D a).trace = fontaineTheta O p ((D.ρM a).trace) := by
    simp only [actH, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  refine ⟨by rw [hH, hT, htr], ?_⟩
  rw [hT]
  simp only [padicToO, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum, RingHom.comp_apply]

end GlobalTheory
