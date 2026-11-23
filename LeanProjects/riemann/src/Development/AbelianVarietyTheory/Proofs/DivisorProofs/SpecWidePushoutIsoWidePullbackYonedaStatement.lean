import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYoneda
import Mathlib
open CategoryTheory Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda : ∀ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ) (ι : Fin (k + 1) → (B →+* T)), (∀ j, (ι j).comp a = (ι 0).comp a) → (∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) → ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A))) (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))), ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) := by
  first | (exact @GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (exact GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (intros; apply GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback  <;> assumption)
