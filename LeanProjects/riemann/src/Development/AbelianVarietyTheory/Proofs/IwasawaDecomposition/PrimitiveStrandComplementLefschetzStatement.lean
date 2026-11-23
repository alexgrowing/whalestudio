import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveStrandComplementLefschetz
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_strand_complement_lefschetz : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (U : ℤ → Submodule ℂ V) (N : Module.End ℂ V) (m : ℕ), iSupIndep U → ⨆ i, U i = ⊤ → (∀ d, ∀ v ∈ U d, N v ∈ U (d + 2)) → (∀ i : ℕ, Set.BijOn (N ^ i) (U (-(i : ℤ))) (U i)) → (∀ k : ℤ, (m : ℤ) < k → U k = ⊥) → IsCompl (strand N (U (-(m : ℤ))) m) (lowPart U N m) := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.isCompl_strand_lowPart | exact GlobalTheory.WeilDeligne.PrimDecomp.isCompl_strand_lowPart | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.isCompl_strand_lowPart <;> assumption)
