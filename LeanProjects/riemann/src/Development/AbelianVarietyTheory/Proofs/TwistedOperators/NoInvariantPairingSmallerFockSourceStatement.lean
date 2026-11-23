import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockSource
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_invariant_pairing_smaller_fock_source : ∀ X : ProvA, admQ5 X → ArchimedeanRallisFifth X → ∀ (t : ℕ) (al be ga de : List ℚ), DataAR t al be ga de → (∀ e ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |e|) → ∀ i : ℕ, 1 ≤ i → i ≤ al.length + be.length → i ≤ ga.length + de.length → ∀ b : Pol (al.length + be.length - i) (ga.length + de.length - i) _ _ →ₗ[ℂ] (X.ds _ _ (lamA' t al be ga de)).HK.V →ₛₗ[starRingEnd ℂ] ℂ, (∀ Z ∈ upq _ _, ∀ P y, b (fockAct2 _ _ _ _ Z P) y + b P ((X.ds _ _ (lamA' t al be ga de)).HK.act Z y) = 0) → b = 0 := by
  first | exact @GlobalTheory.NoInvPairing.no_pairing_smaller_source | exact GlobalTheory.NoInvPairing.no_pairing_smaller_source | (intros; apply GlobalTheory.NoInvPairing.no_pairing_smaller_source <;> assumption)
