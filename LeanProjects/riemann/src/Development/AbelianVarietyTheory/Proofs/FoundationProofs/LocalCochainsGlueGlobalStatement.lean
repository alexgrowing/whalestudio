import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCochainsGlueGlobal
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_cochains_glue_global : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → (∀ v ∈ S, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) → ∃ u : G ℚ Ω → Qbar l, Continuous u ∧ (∀ s, u s ∈ c.O) ∧ (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) ∧ ∀ s t, Cg n (ξ s t) (eps l s * u t - u (s * t) + u s) := by
  first | exact @GlobalTheory.Ord2.TwistTriv.coboundary_of_locTriv | exact GlobalTheory.Ord2.TwistTriv.coboundary_of_locTriv | (intros; apply GlobalTheory.Ord2.TwistTriv.coboundary_of_locTriv <;> assumption)
