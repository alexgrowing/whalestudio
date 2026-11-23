import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumPairsAboveEqAffineHyperplane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_pairsAbove_eq_affineHyperplane : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [AddCommMonoid M] (res : R →+* k) (t : R) (p : Pr R V k) (π : V → W) (φ : Module.Dual k W) (q : W → Pr R V k) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ p.L → x ∈ p.L) → Red res t p.L π → (∀ x ∈ p.L, p.f x = φ (π x)) → (∀ w, φ w = 1 → (q w).Ok res ∧ (q w).IsKer p.L ∧ ∃ e, (q w).f e = 1 ∧ π (t • e) = w) → ∑ᶠ q' ∈ {q' | Pr.Inc res t p q'}, Φ q' = ∑ᶠ w ∈ {w | φ w = 1}, Φ (q w) := by
  first | exact @GlobalTheory.LevelHecke.AboveSum.finsum_above | exact GlobalTheory.LevelHecke.AboveSum.finsum_above | (intros; apply GlobalTheory.LevelHecke.AboveSum.finsum_above <;> assumption)
