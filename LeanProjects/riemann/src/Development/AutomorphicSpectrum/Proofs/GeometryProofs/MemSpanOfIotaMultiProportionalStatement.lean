import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemSpanOfIotaMultiProportional
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_of_iota_multi_proportional : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (b e : Fin n → V) (t : Ω), LinearIndependent Ω e → t ≠ 0 → exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e → ∀ i, b i ∈ Submodule.span Ω (Set.range e) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional | exact GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional | (intros; apply GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional <;> assumption)
