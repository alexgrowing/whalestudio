import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf : ∀ (R : Type) [CommRing R] (J : Ideal R) (W Y : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback b q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → IsClosedImmersion b ∧ b.ker = baseIdeal f J ∧ ∀ V : W.Opens, IsAffineOpen V → Function.Surjective (b.app V).hom ∧ RingHom.ker (b.app V).hom = J.map (cst f V) := by
  first | exact @GlobalTheory.FormalAlg.baseChange_quotient | exact GlobalTheory.FormalAlg.baseChange_quotient | (intros; apply GlobalTheory.FormalAlg.baseChange_quotient <;> assumption)
