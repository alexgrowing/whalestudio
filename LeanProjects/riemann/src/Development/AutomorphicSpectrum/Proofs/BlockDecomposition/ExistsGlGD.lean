import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem gD_mul_gD {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u v : A) :
    gD i u * gD i v = gD i (u * v) := by
  unfold gD
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem gD_one {A : Type} [CommRing A] {t : ℕ} (i : Fin t) : gD i (1 : A) = 1 := by
  unfold gD
  have h : Function.update (1 : Fin t → A) i 1 = 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [h]
  exact Matrix.diagonal_one

theorem det_gD {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u : A) : (gD i u).det = u := by
  unfold gD
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem exists_gl_gD : ∀ {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u : Aˣ),
    ∃ g : GL (Fin t) A, g.1 = gD i (u : A) ∧ Matrix.GeneralLinearGroup.det g = u := by
  intro A _ t i u
  refine ⟨⟨GlobalTheory.CompanionTheory.NullFr.gD i (u : A), GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A), ?_, ?_⟩, rfl, ?_⟩
  · rw [GlobalTheory.CompanionTheory.NullFr.gD_mul_gD, Units.mul_inv, GlobalTheory.CompanionTheory.NullFr.gD_one]
  · rw [GlobalTheory.CompanionTheory.NullFr.gD_mul_gD, Units.inv_mul, GlobalTheory.CompanionTheory.NullFr.gD_one]
  · ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.CompanionTheory.NullFr.det_gD i (u : A)

end GlobalTheory.CompanionTheory.NullFr
