import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetSnocTriangular
import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_snoc_triangular : ∀ {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ) {i : ℕ} (e : Fin (i + 1) → V) (d : Fin i → K) (c : Fin (i + 1) → K), (h.gram σ (Fin.snoc (fun j => d j • e j.castSucc) (∑ k, c k • e k))).det.re = (∏ j, ‖σ (d j)‖ ^ 2) * ‖σ (c (Fin.last i))‖ ^ 2 * (h.gram σ e).det.re := by
  first | exact @GlobalTheory.hermFam_gram_det_triangular | exact GlobalTheory.hermFam_gram_det_triangular | (intros; apply GlobalTheory.hermFam_gram_det_triangular <;> assumption)
