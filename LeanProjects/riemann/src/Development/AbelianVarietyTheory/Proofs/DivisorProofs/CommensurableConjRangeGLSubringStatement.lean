import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommensurableConjRangeGLSubring
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commensurable_conj_range_gl_map_subtype : ∀ {B : Type} [CommRing B] (R : Subring B) (n : ℕ) (c : R), Finite (R ⧸ Ideal.span {c * c}) → ∀ g : GL (Fin n) B, (∀ i j, (c : B) * (g : Matrix (Fin n) (Fin n) B) i j ∈ R) → (∀ i j, (c : B) * ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) → Subgroup.Commensurable ((GeneralLinearGroup.map R.subtype).range.map (MulAut.conj g).toMonoidHom) (GeneralLinearGroup.map R.subtype).range := by
  first | (exact @GlobalTheory.commensurable_conj_range_GL_subring) | (exact GlobalTheory.commensurable_conj_range_GL_subring) | (intros; apply GlobalTheory.commensurable_conj_range_GL_subring  <;> assumption)
