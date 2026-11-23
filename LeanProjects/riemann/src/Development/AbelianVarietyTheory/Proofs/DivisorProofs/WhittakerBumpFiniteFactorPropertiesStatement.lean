import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpFiniteFactorProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerBumpFiniteFactor_properties : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1) → bumpFin (E := E) (n := n) 1 = 1 ∧ (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧ (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧ ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
  first | exact @GlobalTheory.WhitBump.FinBump.bumpFin_props | exact GlobalTheory.WhitBump.FinBump.bumpFin_props | (intros; apply GlobalTheory.WhitBump.FinBump.bumpFin_props <;> assumption)
