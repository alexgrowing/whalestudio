import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoherentSubmodulesGlueFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_submodules_glue_finite : ∀ (Y : Scheme.{0}) [IsIntegral Y] (h : ℕ) (I : Type) (V : I → Y.Opens) (P : ∀ i, Submodule Γ(Y, V i) (Fin h → Γ(Y, V i))), (∀ i, IsAffineOpen (V i)) → (∀ y : Y, ∃ i, y ∈ V i) → (∀ (i j : I) (y : Y), y ∈ V i → y ∈ V j → ∃ k, y ∈ V k ∧ V k ≤ V i ∧ V k ≤ V j) → (∀ (i k : I) (hle : V k ≤ V i), P k = Submodule.span Γ(Y, V k) (piMap (resG Y hle) (Fin h) '' (P i : Set (Fin h → Γ(Y, V i))))) → (∀ i, Module.Finite Γ(Y, V i) (P i) ∧ Module.Projective Γ(Y, V i) (P i)) → ∀ c : Γ(Y, ⊤), c ≠ 0 → (∀ i (x : Fin h → Γ(Y, V i)), resG Y (le_top : V i ≤ ⊤) c • x ∈ P i) → GlobalTheory.VB.IsVB (glueSub V P).toMod h := by
  first | exact @GlobalTheory.LatGlue.isVB_glueSub | exact GlobalTheory.LatGlue.isVB_glueSub | (intros; apply GlobalTheory.LatGlue.isVB_glueSub <;> assumption)
