import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGenerator
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_lattice_generator : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p → L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} ∧ exteriorPower.ιMulti Ω r b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti | exact GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti <;> assumption)
