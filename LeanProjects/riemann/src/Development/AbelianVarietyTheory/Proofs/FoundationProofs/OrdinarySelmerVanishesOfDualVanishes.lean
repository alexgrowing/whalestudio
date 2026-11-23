import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualSelmerClassesUnboundedOrderStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerUnboundedOrderNonzeroOrdinaryClassStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem grZero_of_grZero_dual1 : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l),
    Nf e S A W → GrZero (dual1 W) A → GrZero W A := by
  intro hL l _ Ω _ _ _ e S A W hN hD
  by_contra hW
  obtain ⟨c, hc, hm⟩ := GlobalTheory.T.exists_dualSelmer_classes_unbounded_order hL l Ω e S A W hN hW
  exact GlobalTheory.T.dualSelmer_unbounded_order_nonzero_ordinaryClass hL l Ω e S A W hN c hc hm hD

end GlobalTheory.Ord2
