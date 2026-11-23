import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectiveOfFreeLatticeOverFiniteFreeRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_of_free_lattice_over_finite_free_ring : ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  first | exact @GlobalTheory.projective_compHom_of_free_of_finite_free | exact GlobalTheory.projective_compHom_of_free_of_finite_free | (intros; apply GlobalTheory.projective_compHom_of_free_of_finite_free <;> assumption)
