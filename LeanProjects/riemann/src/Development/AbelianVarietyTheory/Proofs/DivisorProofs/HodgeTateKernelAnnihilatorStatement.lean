import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAnnihilator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_kernel_annihilator : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), (∀ x : P.V, (∀ y ∈ P.W, P.pairV x y = 0) ↔ x ∈ Submodule.span C (Set.range P.bLie)) ∧ Module.finrank C (Submodule.span C (Set.range P.bLie)) + Module.finrank C P.W = 2 * P.A.g := by
  first | exact @GlobalTheory.HTLat.AnnKer.annW_eq_span_bLie | exact GlobalTheory.HTLat.AnnKer.annW_eq_span_bLie | (intros; apply GlobalTheory.HTLat.AnnKer.annW_eq_span_bLie <;> assumption)
