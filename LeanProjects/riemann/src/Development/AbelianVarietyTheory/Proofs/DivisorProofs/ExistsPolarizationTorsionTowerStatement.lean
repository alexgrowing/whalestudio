import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationTorsionTower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarization_torsion_tower : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), WeilIntegralFinite P → ∀ (G : PDivGroup p O) (tw : G.TorsionTower P.Gt), ∃ φ : G ⟶ G.dual, ∀ (s s' : G.Tate) (n : ℕ), algebraMap O C (muRoot (pairing G O s (tateMap G G.dual O φ s')) n) = (weil P.A (p ^ n) (P.toA (GlobalTheory.DeRham.spOver (s.pt n) ≫ tw.y n)) (P.toA (GlobalTheory.DeRham.spOver (s'.pt n) ≫ tw.y n)) : C) := by
  first | exact @GlobalTheory.WeilPhi.exists_hom_weil | exact GlobalTheory.WeilPhi.exists_hom_weil | (intros; apply GlobalTheory.WeilPhi.exists_hom_weil <;> assumption)
