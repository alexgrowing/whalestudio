import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulAlgebraTraceDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspacesOfRingHomsIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumActionsRingHomsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrRepEigenspacesSpanTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumTraceEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulAlgebraTraceStatement

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eig_decomp_T_H : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), (iSupIndep (fun σ : Λ →+* O => eig C (actT D) σ) ∧ (⨆ σ : Λ →+* O, eig C (actT D) σ) = ⊤ ∧ ∀ τ : Λ →+* O, Module.finrank C (eig C (actT D) τ) = N) ∧ (iSupIndep (fun σ : Λ →+* O => eig C (actH D) σ) ∧ (⨆ σ : Λ →+* O, eig C (actH D) σ) = ⊤ ∧ ∀ τ : Λ →+* O, Module.finrank C (eig C (actH D) τ) = N) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D
  obtain ⟨⟨ρT, hρT⟩, ⟨ρH, hρH⟩⟩ := GlobalTheory.T.sandwich_datum_actions_ring_homs p O ε Λ h D
  have hT : ∀ a, (ρT a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a) := by
    intro a
    rw [congrFun hρT a, (GlobalTheory.T.sandwich_datum_trace_eq p C v O hv ε hε Λ h D a).2, GlobalTheory.T.rep_trace_eq_mul_algebra_trace p Λ N h hh D.ρT a,
      map_mul, map_natCast]
  have hH : ∀ a, (ρH a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a) := by
    intro a
    rw [congrFun hρH a, (GlobalTheory.T.sandwich_datum_trace_eq p C v O hv ε hε Λ h D a).1,
      (GlobalTheory.T.sandwich_datum_trace_eq p C v O hv ε hε Λ h D a).2, GlobalTheory.T.rep_trace_eq_mul_algebra_trace p Λ N h hh D.ρT a,
      map_mul, map_natCast]
  rw [← hρT, ← hρH]
  exact ⟨⟨GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ h ρT hv.hom_inj, GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ h ρT,
      GlobalTheory.T.rep_trace_eq_mul_algebra_trace_dvr p C v O hv Λ N h ρT hT⟩,
    ⟨GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ h ρH hv.hom_inj, GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ h ρH,
      GlobalTheory.T.rep_trace_eq_mul_algebra_trace_dvr p C v O hv Λ N h ρH hH⟩⟩

end GlobalTheory
