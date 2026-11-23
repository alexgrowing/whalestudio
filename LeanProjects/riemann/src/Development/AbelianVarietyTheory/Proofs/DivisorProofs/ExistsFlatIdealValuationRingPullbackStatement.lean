import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatIdealValuationRingPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsAlt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_ideal_valuationRing_pullback : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X'] (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X), IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))) → ∀ I : Ideal Γ(X', ⊤), ∃ J : Ideal Γ(X, ⊤), ((Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat ∧ Ideal.map b.appTop.hom J = I := by
  first | exact @GlobalTheory.FlatHilbAff.exists_flat_ideal | exact GlobalTheory.FlatHilbAff.exists_flat_ideal | (intros; apply GlobalTheory.FlatHilbAff.exists_flat_ideal <;> assumption)
