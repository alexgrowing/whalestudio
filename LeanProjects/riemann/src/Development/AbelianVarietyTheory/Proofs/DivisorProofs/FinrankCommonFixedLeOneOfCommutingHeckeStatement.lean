import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCommonFixedLeOneOfCommutingHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_commonFixed_le_one_of_commuting_hecke : ∀ (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Monoid (H c)] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V), (∀ c, e c * e c = e c) → (∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g)) → (∀ c c', c ≠ c' → Commute (e c) (e c')) → (∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h)) → (∀ c g h, e c * a c g * e c * a c h * e c = e c * a c h * e c * a c g * e c) → (∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤) → ∀ W : Submodule ℂ V, (∀ v ∈ W, ∀ c, e c v = v) → finrank ℂ W ≤ 1 := by
  first | exact @GlobalTheory.CommutingHecke.finrank_fixed_le_one | exact GlobalTheory.CommutingHecke.finrank_fixed_le_one | (intros; apply GlobalTheory.CommutingHecke.finrank_fixed_le_one <;> assumption)
