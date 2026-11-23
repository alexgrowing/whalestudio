import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatQuasiSection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_flat_quasi_section : ∀ (S : Type) [CommRing S] [HenselianLocalRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of S)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f], (∃ y : Y, f y = IsLocalRing.closedPoint S) → ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A), Module.Finite S A ∧ Module.Flat S A ∧ Nontrivial A ∧ ∃ h : Spec (.of A) ⟶ Y, h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S A)) := by
  first | exact @GlobalTheory.exists_finite_flat_spec_of_quasiFinite_of_henselian | exact GlobalTheory.exists_finite_flat_spec_of_quasiFinite_of_henselian | (intros; apply GlobalTheory.exists_finite_flat_spec_of_quasiFinite_of_henselian <;> assumption)
