import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleMembershipLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submodule_membership_local : ∀ (Y : Scheme.{0}) (h : ℕ) (W : Y.Opens), IsAffineOpen W → ∀ (T : Submodule Γ(Y, W) (Fin h → Γ(Y, W))) (v : Fin h → Γ(Y, W)), (∀ y ∈ W, ∃ (W' : Y.Opens) (hle : W' ≤ W), y ∈ W' ∧ piMap (resG Y hle) (Fin h) v ∈ Submodule.span Γ(Y, W') (piMap (resG Y hle) (Fin h) '' (T : Set (Fin h → Γ(Y, W))))) → v ∈ T := by
  first | exact @GlobalTheory.LatGlue.mem_of_locally_mem_span_res | exact GlobalTheory.LatGlue.mem_of_locally_mem_span_res | (intros; apply GlobalTheory.LatGlue.mem_of_locally_mem_span_res <;> assumption)
