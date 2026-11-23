import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatum
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (h : ℕ) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (fil : G.dual.omega ≃ₗ[O] D.Fil), (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O)) → ∃ L : (Fin h → Ainf p O) ≃ₗ[Ainf p O] latt G, ∀ r t, (L r).1 t = r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i)) := by
  first | exact @GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace | exact GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace | (intros; apply GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace <;> assumption)
