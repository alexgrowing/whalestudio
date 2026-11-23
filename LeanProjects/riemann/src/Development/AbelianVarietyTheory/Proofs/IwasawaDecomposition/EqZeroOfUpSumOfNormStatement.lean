import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfUpSumOfNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_sum_inc_eq_zero_of_sum_dil_eq_zero : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [Fintype k] [DecidableEq k] [Finite W] [AddCommGroup M] [Module ℂ M] (res : R →+* k) (t : R) (Λ : Submodule R V) (π : V → W) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) → Red res t Λ π → (∀ g : Module.Dual k W, g ≠ 0 → ∃ d : Pr R V k, d.L = Λ ∧ (∀ x ∈ Λ, d.f x = g (π x)) ∧ ∑ᶠ q ∈ {q | Pr.Inc res t d q}, Φ q = 0) → (∀ q : Pr R V k, q.Ok res → q.IsKer Λ → ∑ a : kˣ, Φ (q.dil (a : k)) = 0) → ∀ q : Pr R V k, q.Ok res → q.IsKer Λ → Φ q = 0 := by
  first | exact @GlobalTheory.LevelHecke.eq_zero_of_upSum_of_norm | exact GlobalTheory.LevelHecke.eq_zero_of_upSum_of_norm | (intros; apply GlobalTheory.LevelHecke.eq_zero_of_upSum_of_norm <;> assumption)
