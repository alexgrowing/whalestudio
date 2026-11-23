import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteFreeAlgebraAffineExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpecFiniteFreeOfFiniteFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCoverStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem main : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro S Z z hfin hflat hlfp r
  refine GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover S Z z hfin hflat hlfp r fun s => ?_
  obtain ⟨W, A, B, _, _, _, _, _, eW, eZ, hs, hc⟩ := GlobalTheory.T.exists_local_spec_finite_free_of_finite_flat S Z z hfin hflat hlfp s
  refine ⟨W, hs, GlobalTheory.T.isHilbertSchemeRepresentable_of_iso (z ∣_ W) (Spec.map (CommRingCat.ofHom (algebraMap A B))) eW.symm eZ.symm ?_ r
    (GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists A B r)⟩
  rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end GlobalTheory.HilbertSch
