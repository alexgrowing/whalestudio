import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieBundleIntersection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    ∀ x : X, ∑ᶠ O : {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) //
        (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x},
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O.1)) : ℂ)) *
          f (Quotient.out O.1).elt (Quotient.out O.1).pt =
      (1 / (Nat.card (MulAction.stabilizer H x) : ℂ)) * ∑ᶠ γ : H, f γ x := by
  first | exact @GlobalTheory.PtFib.ptFib_mass | exact GlobalTheory.PtFib.ptFib_mass | (intros; apply GlobalTheory.PtFib.ptFib_mass <;> assumption)
