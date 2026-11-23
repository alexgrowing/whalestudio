import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerModPrimePowInjectsResidualSelmer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∃ cls : (G ℚ Ω → Fin 2 → Qbar l) → H1 (rhoS c n W hint S hN), (∀ y, GwCount.SelN c n S A W y → cls y ∈ SelG c n W hint S hN A) ∧ ∀ y y', GwCount.SelN c n S A W y → GwCount.SelN c n S A W y' → cls y = cls y' → Cob1 c n W ⊤ (y - y') := by
  first | exact @GlobalTheory.Ord2.SelLower.sel_lower | exact GlobalTheory.Ord2.SelLower.sel_lower | (intros; apply GlobalTheory.Ord2.SelLower.sel_lower <;> assumption)
