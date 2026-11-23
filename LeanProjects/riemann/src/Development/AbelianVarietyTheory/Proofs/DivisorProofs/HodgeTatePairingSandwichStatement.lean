import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_pairing_sandwich : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate) (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]), v.Integers O → Function.Bijective (fun a : ℤ_[p] => a • ζ) → (∀ s χ, pairing G O s χ = B s χ • ζ) → (∀ x : O ⊗[ℤ_[p]] G.Tate, G.hodgeTateLinear x = 0 ↔ ∃ (c : O) (y : G.Lie), c ≠ 0 ∧ ∀ χ, c * (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog (G := G) χ)) ∧ Module.finrank O (LinearMap.ker G.hodgeTateLinear) + Module.finrank O (LinearMap.ker G.dual.hodgeTateLinear) = G.height := by
  first | exact @GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear | exact GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear | (intros; apply GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear <;> assumption)
