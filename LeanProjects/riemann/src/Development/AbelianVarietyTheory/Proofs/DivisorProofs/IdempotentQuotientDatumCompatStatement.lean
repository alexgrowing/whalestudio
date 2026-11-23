import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentQuotientDatumCompat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_quotient_datum_compat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (π : Γ →ₐ[ℤ_[p]] Λ) (e : Γ), IsIdempotentElem e → Function.Surjective π → RingHom.ker π = Ideal.span {1 - e} → ∀ (h : ℕ) (D : Datum ε h Γ), ∃ (h' : ℕ) (D' : Datum ε h' Λ) (iT : Matrix (Fin h) (Fin h') ℤ_[p]) (pT : Matrix (Fin h') (Fin h) ℤ_[p]) (iM : Matrix (Fin h) (Fin h') (Ainf p O)) (pM : Matrix (Fin h') (Fin h) (Ainf p O)), pT * iT = 1 ∧ iT * pT = D.ρT e ∧ pM * iM = 1 ∧ iM * pM = D.ρM e ∧ D'.F = pM * D.F * iT.map (ofPadic p O) ∧ D'.G = pT.map (ofPadic p O) * D.G * iM ∧ (∀ x, D'.ρT (π x) = pT * D.ρT x * iT) ∧ ∀ x, D'.ρM (π x) = pM * D.ρM x * iM := by
  first | exact @GlobalTheory.DetInv.datum_idempotent_part | exact GlobalTheory.DetInv.datum_idempotent_part | (intros; apply GlobalTheory.DetInv.datum_idempotent_part <;> assumption)
