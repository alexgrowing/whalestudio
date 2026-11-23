import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffine
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zariskiConnectedness_isPreconnected_fibre_affine : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) [IsProper f] [IsAffine X] [IsLocallyNoetherian X], Function.Bijective f.appTop → ∀ x : X, _root_.IsPreconnected (f.base ⁻¹' {x}) := by
  first | exact @GlobalTheory.ZariskiConn.isPreconnected_fibre | exact GlobalTheory.ZariskiConn.isPreconnected_fibre | (intros; apply GlobalTheory.ZariskiConn.isPreconnected_fibre <;> assumption)
