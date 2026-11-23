import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualCocyclesModPrimePowUnramifiedOutsideSBou
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded_alt : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B := by
  first | exact @GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded | exact GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded | (intros; apply GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded <;> assumption)
