import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootTiltLatticeBound
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.CyclicRecursionStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_span_rhoM_rhoT_mulVec_eq_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ], ∀ (h : ℕ) (D : Datum ε h Λ), ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ), ∃ (N : ℕ) (x : Fin N → Fin h → Ainf p O) (y : Fin N → Fin h → ℤ_[p]), h = N * d ∧ Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => D.ρM (b ij.2) *ᵥ x ij.1) = ⊤ ∧ Submodule.span ℤ_[p] (Set.range fun ij : Fin N × Fin d => D.ρT (b ij.2) *ᵥ y ij.1) = ⊤ := by
  first | exact @GlobalTheory.DetInv.exists_span_top_of_datum | exact GlobalTheory.DetInv.exists_span_top_of_datum | (intros; apply GlobalTheory.DetInv.exists_span_top_of_datum <;> assumption)
